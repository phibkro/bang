<!-- note-status: active -->
# calc / json on the compiled + emitted paths — diagnosis

> **DIAGNOSIS probe** (deliverable = root causes + fix plan; no code fixes this lane).
> Measured on a clean clone of `main @ ccec47e9`, 2026-07-11T19:57Z, `nix develop`,
> `lake build` EXIT 0 (760 jobs). Every row below is a RUN outcome, not a reading.
> Repros + the merged-emit probe live in `scratch/calcjson/`.

## TL;DR — the headline call

- **`--compiled` (exec∘compile): DONE for BOTH.** calc = `11021193`, json = `163`,
  byte-identical to `bang run` (env) and `--engine=oracle`. The calc-findings "hang"
  and the json-findings "both engines hang" are **STALE** — both dissolved by #95
  (knot-sharing, 2026-07-10) which post-dates both notes. This is the free win.
- **emitModuleGC→wasmtime: json is ONE HARNESS-FIX (S) away; calc hits a GENUINE
  SEMANTIC WALL (L).**
  - **json** emits cleanly and **runs on wasmtime → `163` == expected.txt**, once
    the emitter is fed a *module-resolved* `Comp` (proven this lane, see the probe).
    The only blocker is that the emit harness doesn't resolve `import`s.
  - **calc** is blocked by **first-class capabilities**: `Eval.eval`/`countSteps`
    take `tr : Cap Eval_Trace` as a **value parameter** and `perform` `tr.log(..)`
    on it. The GC emitter only lowers a `perform` whose cap is a *lexical* handler
    binding (`WasmEmit.lean:962` NAMED refusal). This is a rung-5+ rep, not a bug.
- **hostio-echo**: expected-refuse CONFIRMED (host-IO op `con.print`/`readLine` has
  no GC lowering — the ADR-0104 boundary). Set aside per brief.

So "**the dogfood programs run compiled on wasmtime**" splits: json is **S**
(shippable now with a small harness change); calc is **L** (needs the first-class
-capability GC rep, a genuine rung-5+ feature). "Dogfood **runs `--compiled`**" is
**already TRUE** for both — a launch-grade claim available today.

## The measurement matrix (all RUN, bounded by `timeout`)

| program | `bang run` (env) | `--engine=oracle` | `--compiled` | emit (merged→wasmtime) |
|---|---|---|---|---|
| **calc** | `11021193` (0s) | `11021193` (8s) | **`11021193` (8s)** ✅ | **EMIT-REFUSED** (cap-as-arg) ❌ |
| **json** | `163` (0s) | `163` (2s) | **`163` (2s)** ✅ | **`163` on wasmtime** ✅ (needs harness merge) |
| hostio-echo | `ih` (host sim) | — | — | refuse (host-IO op, ADR-0104) — set aside |

`--compiled` fuel = `compiledFuel = 1_000_000` (Main.lean:70); no fuel exhaustion,
no hang — both terminate in single-digit seconds. **The dogfood notes' hangs are
gone.**

## Wall table (program × path × wall × class × fix locus × size)

| # | program | path | wall (exact) | class | fix locus | size | owner |
|---|---|---|---|---|---|---|---|
| W1 | calc | `--compiled` | ~~hang~~ | **(a) STALE** — fixed by #95 | — (re-ran green) | — | — |
| W2 | json | `--compiled` | ~~both-engine hang~~ | **(a) STALE** — fixed by #95 | — (re-ran green) | — | — |
| W3 | json | emit | `LOWER-ERROR: 'tagAt': type variable unresolved` **only when un-merged**; merges away | **(d) emitter-harness gap** (no module resolution) | `scratch/Rung4Shape.lean:20 lowerEntry` — reuse `Main.resolveEntryFileRaw`+`mergeModules`; or add `bang emit` subcommand | **S** | compiler-engineer / harness |
| W4 | calc | emit | `EMIT-REFUSED: perform op 'log' on a cap threaded as a runtime VALUE (vvar 1 = a value/arg slot, not a lexical handler cap) — first-class-capability rep is rung-5+` | **(e) GENUINE semantic wall** (first-class caps) | `Bang/Backend/WasmEmit.lean:962` (`emitCompGC` perform arm) | **L** | kernel/compiler-engineer (rung-5+) |
| W5 | calc | emit | (also) `LOWER-ERROR: unbound variable Ast` when un-merged | **(d) same harness gap as W3** | same as W3 | (subsumed by S) | — |
| W6 | hostio-echo | emit | host-IO op has no GC lowering | **(e) by design** (ADR-0104 host boundary) | n/a — expected refusal | — | — |

## Minimized repros (the discriminator, isolated)

Two 3–8-line single-file programs (`scratch/calcjson/`) pin the calc wall to
**cap-as-argument vs cap-lexical**, holding everything else fixed:

| repro | shape | env / compiled | emit |
|---|---|---|---|
| `cap-as-arg.bang` | `let rec go : Cap Trace -> Int -> Int` performs `tr.log` on a **param** `tr` | `4` / `4` | **EMIT-REFUSED** (the calc wall) |
| `cap-lexical.bang` | `handle (let a = tr.log(1) …) with Trace as tr {…}` — cap used in its own **lexical** scope | `2` / `2` | **emits + runs on wasmtime → `2`** |

The ONLY difference is where the cap comes from. A `perform` on a lexically-bound
handler cap lowers (this is the whole S4 rung-5 custom-effects corpus,
`emit-rung5-print-diff.sh`); a `perform` on a cap that arrived as a function
argument does not — the static GC emitter routes caps by de-Bruijn *handler*
binder, and a value-slot cap has no handler frame to route to.

## Why the calc wall is REAL (not another stale/harness item)

- calc's `Eval.eval` (line 10) and `countSteps` (line 24) are
  `Cap Eval_Trace -> … ! {Div, Eval_Trace}` — the cap is the **first curried
  parameter**, threaded through every recursive call (`$eval tr env a`), and
  `main` passes it as a value into the `handle`. This is the *documented* good
  surprise of the calc dogfood ("a user effect woven structurally into a
  recursive traversal") — and it is exactly the first-class-capability shape.
- The kernel/CalcVM handle it fine (that is why `--compiled` = `11021193`): the
  cap is a runtime `vcap` value there. The **emitter** is a *static* lowering with
  no runtime cap value in its `$val` GC rep (`WasmEmit.lean:764` also refuses a
  bare `vcap`). Giving the GC path a first-class cap means either (a) a `$cap` GC
  struct carrying identity+the resume closure, threaded as an ordinary `$val`, and
  a `perform` that dispatches on it at runtime; or (b) a defunctionalized /
  closure-converted handler-passing pass before emit. Both are rung-5+ scope,
  matching the emitter's own refusal text.

## Interaction: does fixing json's emit unlock calc's?

**No — independent walls.** W3 (json, harness) and W4 (calc, semantic) share
nothing:

- Fixing the **harness** (module resolution → merged `Comp`) unlocks **json emit
  fully** and gets **calc PAST `LOWER-ERROR` to the real `EMIT-REFUSED`** (W5→W4) —
  i.e. it converts calc's blocker from a harness artifact into the true semantic
  wall, but does **not** emit calc.
- Fixing **calc** needs the first-class-cap GC rep (W4), which json never
  exercises (json's `main` is pure parse+print+tag — **no effects/handlers at
  all**; that is precisely why it emits today).

## Recommended fix order (cheapest real win first)

1. **[S] Wire module resolution into the emit path** — reuse `Main`'s
   `resolveEntryFileRaw` + `mergeModules` (or, cleaner, add a `bang emit <file>
   [out.wat]` subcommand so the emitter shares the runner's resolution instead of
   the `rung4-shape` scratch exe). **This alone lands "json compiles to WasmGC and
   runs on wasmtime == bang run" as a launch-grade claim** — proven this lane
   (`scratch/calcjson/EmitMerged.lean` did exactly this and wasmtime printed
   `163`). Add json to the `emit-rung5-print-diff.sh` corpus once resolution is in.
2. **[free] Land the `--compiled` dogfood claim now** — add calc+json to
   `check-examples`-style gating on `--compiled` (they already pass). No code; a
   test-wiring change. Kills the stale "compiled hangs" findings.
3. **[L, post-v1] First-class-capability GC rep** — the calc emit wall. Genuine
   rung-6 feature (a `$cap` value + runtime dispatch, or handler-passing
   closure-conversion). Track as the named successor to the S4 custom-effects work;
   do NOT block the tag on it.

## Stale-findings correction (say it loud)

- `dogfood-calc-findings.md` §"CORRECTNESS — --compiled hangs": its own **FIXED
  (#95)** addendum is now confirmed by re-run — calc `--compiled` = `11021193` in
  8s. The top-level SUMMARY still lists it as a live "Correctness (non-gate): 2";
  that first item is now fully closed.
- `dogfood-json-findings.md` §"BLOCKER — composing … hangs both engines": **STALE**.
  json `main.bang` runs on **all three engines** (`163`) and **emits to wasmtime**.
  The both-engine hang was the same #95 super-linear residual-recompile cost.

Both notes predate #95's 2026-07-10 landing (the calc note carries the fix
addendum; the json note does not) and the module-system + monomorphization
landings. Their friction catalogues (fmt-`$(Mod.op)`, wildcard arms, arity ≤ 2,
mutual let-rec) remain valid — only the **compiled-hang** entries are stale.

## Artifacts (all under `scratch/calcjson/`)

- `EmitMerged.lean` — the merged-emit probe (resolve→`mergeModules`→
  `checkAndLowerProg`→`emitModuleGCPrint`); mirrors `Main.resolveEntryFileRaw`.
  Running it prints calc = EMIT-REFUSED, json = EMIT ok + writes `JSON.wat`.
- `JSON.wat` — the emitted WasmGC module; `wasmtime run … JSON.wat` → `163`.
- `cap-as-arg.bang` / `cap-lexical.bang` — the minimized discriminator pair.
