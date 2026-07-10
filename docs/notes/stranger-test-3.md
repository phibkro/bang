<!-- note-status: active -->
# Stranger test — round 3 (2026-07-10)

> Third outer-loop probe, over today's landed wave (main @ `6192ff1`). Same repeatable
> method as rounds 1–2 (`stranger-test-1.md`, `stranger-test-2.md`): a zero-prior agent,
> roleplay-strict — README → install → **generated reference** (`docs/reference/language.md`)
> → `examples/` → CLI output ONLY; NO `Bang/*.lean`, `CLAUDE.md`, `CONTEXT.md`, `docs/notes/`,
> `docs/decisions/`. Where the surface fails, that failure IS the finding. Round 3's new
> surface: the **Stage-7 user-defined-effect handle-with syntax** (ADR-0095, landed hours ago
> — the likeliest gap), plus driving **`bang query`** and **`bang rewrite`** from their
> reference sections, and the claim-vs-verifiable pass (`just verify` / `just axioms`).

## Verdict

**7/10 ship-ability** — unchanged from round 2's 7.0, but the *composition* moved: round-2's
two headline blockers (laws unreachable, check-json spans lost) are **substantially fixed**,
and were replaced by a new pair on the just-landed Stage-7 surface. The tooling wave (`bang
query`, `bang rewrite`) is genuinely excellent and shipped documented. The user-effect surface
works for the exact single-op shape the three examples cover and **breaks the moment you step
one inch past them** (a second operation), while being taught only by those examples — the
round-1/round-2 pattern, third time running.

## The one doc change (the round's headline)

**The user-defined-effect surface has NO entry in the generated reference** (issue #88). The
`effect Name { op : T }` declaration, the `handle e with Name as h { op(args) => body }`
install, the `h.op(args)` perform, and the resumption contract are all reverse-engineered from
`examples/handle-custom-{tracer,resume,abort-coexist}/` — the reference's Surface-syntax table
still shows only the old single-arg `handle e`, and its grammar's `handle` rule is the pre-Stage-7
`handle [as <ident>] <expr>` shape. The word `effect` never appears as a surface DECL keyword.
This is the exact round-1 (strings, #65) / round-2 (modules) gap: the feature works, the
reference doesn't teach it. Fix = a build-gated **"User-defined effects" section** in
`language.md`.

## Findings ranked by real friction

Severity: **S1** ships-broken/false-doc · **S2** blocks a documented journey from the outside ·
**S3** friction/regression · **S4** cosmetic.

1. **[S1] Multi-clause handlers are broken — 2+ ops fail even with bare bodies (issue #86, NEW).**
   Every landed `handle-custom-*` example is single-op/single-clause; the multi-clause path
   shipped unexercised and does not work:
   ```
   effect Two { a : Int -> Int ; b : Int -> Int }
   handle two.a(5) with Two as two { a(n) => n  b(n) => n }
   -- bang run → error: let-binding '#p': unbound variable n     (perform only 'a'!)
   handle two.a(5) with Two as two { a(n) => n+1  b(n) => n+1 }
   -- bang run → error: app: callee is not a function
   ```
   The clause binder `n` is lost the moment a second clause exists — even a trivial `a(n) => n`
   body, even when only one op is performed. The matrix:
   | clause shape | result |
   |---|---|
   | 1op, bare `n` | `5` ✓ |
   | 1op, `n + 1` | `6` ✓ |
   | 1op, nested `n + n*2` | `unbound variable n` (= existing **#85**) |
   | **2op, bare bodies** | **`let-binding '#p': unbound variable n`** ← #86 |
   | **2op, binop bodies** | **`app: callee is not a function`** ← #86 |
   Same disease family as #85 (clause-binder Γ threading) but a DIFFERENT, more fundamental
   trigger (#85 is single-op + nested binop). The effect decl parses+registers fine (`dump`
   shows both ops); the failure is at elaboration, on both engines. A multi-op effect is the
   natural shape for any real effect (Reader `ask`+`local`, Logger `info`+`warn`, State
   `get`+`put`), so today only single-op user effects work end-to-end.

2. **[S2/doc] Parameter-carrying handler `(Name init)` — init value is unreachable; the README
   claims a phantom `param` binder (issue #87, NEW).** The `with (Reader 100) as net` form
   accepts an init but nothing binds it in a clause body:
   ```
   handle cfg.ask(0) with (Cfg 42) as cfg { ask(x) => x + param }   -- → unbound variable param
   -- and the init is inert: (R 100) and (R 999) both ⟹ 6 when the body ignores it
   ```
   `examples/handle-custom-resume/README.md` says *"`fetch(x)` resumes with `x + param`
   (`param` names the carried `100`)"* — but the example body hardcodes the literal `100`,
   never writes `param`, and `param` doesn't exist. Either bind the init (the parameter-carrying
   story) or drop the form + fix the README. Batched in the same issue: **effect op names
   silently collide with reserved keywords** — `get`/`put`/`new`/`read`/`write`/`raise`/`handle`
   can't be op names (a stranger modeling a Reader reaches for `get`/`read`/`ask`; half are
   landmines). Loud parse error, but undocumented.

3. **[S3] fresh-clone `just verify` exits 1 on `check-git-hygiene` (issue #89, NEW).**
   ONBOARDING §8 sells `just verify` as *"the single command tells the full story"*, but on a
   fresh clone it red-exits because `gc.auto`/`gc.autoDetach` aren't set (that's `just setup`'s
   job). Everything substantive on that same run passed — selfcheck, `lake build` (1442 jobs),
   all 12 examples, the trait-law proofs. Only the multi-worktree-corruption guard misfires on
   a single standalone clone. Self-corrects after `git config gc.auto 0 && gc.autoDetach false`;
   logged so the "full story" claim stays true for a first-timer.

4. **[S4] `bang query` verb output shapes drift slightly from the reference.** `symbols`
   returns its array under key `"symbols"` (reference says it's "`dump`'s own `decls` array");
   `refs <name>` returns `{"name","kind"}` records, not the `{"from","to"}` edge shape `dump`/the
   reference describe. Both are usable, but a stranger composing scripts across `dump` and the
   curated verbs hits the key/shape mismatch. Cosmetic — the facts are all present.

5. **[S4] `bang rewrite rename -w` writes a file with no trailing newline.** The `-w` output
   ends `…triple 21` with no `\n` (git shows "no newline at end of file"). Cosmetic.

## What worked (preserve these properties)

- **`bang query` (all six verbs) is excellent and shipped documented.** `dump`/`symbols`/`type`/
  `def`/`refs`/`effects` all ran, matched the documented versioned schema (`schemaVersion:1`,
  `bangVersion:"0.1.0"`, flat fact arrays), and the reference's own `jq` composition worked.
  The dump-as-fact-base contract is real and testable from the outside.
- **`bang rewrite` is excellent — the moat feature demonstrably fires.** `fmt`/`rename` emit
  clean unified diffs, touch nothing without `-w`, and both loud diagnostics (collision,
  nonexistent) fire. The **differential preservation gate caught a real hazard**: renaming a
  top-level to collide with a local binder aborted with *"preservation: rewritten program FAILED
  TO ELABORATE … the rewrite is unsound, aborting"*. The CQS read/command split works end to end.
- **The single-op user-effect surface works on both engines.** `handle-custom-{tracer,resume,
  abort-coexist}` all run (30/106/42); a self-authored single-op effect performed three times
  ⟹ 60; the good-path dispatch error is outstanding (`unknown operation 'emitt' for effect
  'Log'`).
- **`bang test` laws now REACH PASS (round-2's #74 headline substantially resolved).** Following
  the diagnostic's own hint (non-Int target + `==` in the law body), `✓ Eq.refl — PASS (30
  samples)`. Round 2 never reached a single PASS; now the ERROR messages *teach the workaround*
  (`impl 'Eq' for Int … aliases a built-in operator …`; `law calls trait op 'eq' directly —
  trait ops are invoked ONLY through their overloaded operator in v1`) and the workaround works.
- **check --json spans FIXED (round-2's S3 regression resolved).** Type-mismatch now carries a
  span (`1 + ()` → `span:{line:1,col:5}`, `code:"type"`); file parse errors carry `code:"parse"`
  + a real span (round 2 saw `span:null` + mislabeled `code:"type"`). The round-1 property is back.
- **The ~90 build-gated `#guard` reference examples + the 12-project example oracle all pass** —
  the docs' superpower (drift = failing diff) is intact; `just check-examples` is green.
- **`--version` is `bang 0.1.0`** (round 2 saw `0.1.0-dev`); `--help`/`--version` exit 0.

## Comparison vs round-2

| round-2 finding | round-3 status |
|---|---|
| **[S2] `bang test` laws unreachable** (no PASS from outside) | **SUBSTANTIALLY FIXED** — PASS reachable via the (now-taught) non-Int + `==` workaround (#74 diagnostics are excellent) |
| **[S3] check --json type-mismatch span lost + file parse mislabeled `type`** | **FIXED** — spans present, `code:"parse"` correct |
| [S1] `pub` visibility unenforced | not re-tested (round-3 scope = Stage-7); still tracked as #73, now honestly documented as a "known v1 limitation" in the reference's Modules section |
| modules undocumented in reference | **FIXED** — a full "Modules (ADR-0093)" section now present |
| **user-effect handle-with surface** | **NEW** — works single-op; undocumented in reference (#88) + multi-op broken (#86) + param-init inert (#87) |
| `just verify` on a fresh clone | **NEW** — red-exits on git-hygiene pre-`setup` (#89) |

## Score breakdown (/10)

| dimension | round-2 | round-3 | note |
|---|---|---|---|
| install / orient | 1.0 | 0.75 | README build path clean, `--version` fixed; `just verify` misfires on fresh clone (#89) |
| language-expression surface | 2.0 | 2.0 | strings/comments/arith/modules/let all exact |
| user-effect journey (Stage-7) | — | 0.75 | single-op works both engines; multi-op broken (#86), param inert (#87), undocumented (#88) |
| laws journey (`bang test`) | 0.5 | 1.25 | PASS now reachable; diagnostics teach the path |
| tooling: `query` + `rewrite` | — | 1.5 | both excellent, documented; preservation gate fires; minor shape drift (S4) |
| error actionability | 1.5 | 1.5 | runtime terminals + law diagnostics outstanding |
| agent loop (`check --json`) | 1.0 | 1.25 | spans restored across type-mismatch + file parse |
| fmt / conformance / docs-trust | 1.0 | 1.0 | idempotent, value-preserving, gated corpus green (#77 qualified-paren-drop still open) |
| **total** | **7.0** | **~7.0** | tooling ↑, laws ↑, check-json ↑; user-effect surface + verify-misfire ↓ |

## The blind-spot list (what the docs still don't teach a stranger)

- **User-effect surface** — the whole `effect`/`handle-with`/`h.op` triad (#88).
- **Resumption model** — clause-body-value = one-shot tail resume; no `resume` keyword. Only
  example prose says so.
- **Reserved op names** — `get`/`put`/`new`/`read`/`write`/`raise`/`handle` can't be op names.
- **Multi-op is broken** — the reference (once it documents effects) must note #86 until fixed,
  the way it honestly notes #73/#74.
- **`(Name init)` semantics** — what the init does, whether it's readable (#87).

## Method note (repeatable)

Same protocol as rounds 1–2 (roleplay-strict + forbidden-files + verbatim-stumbles + "one doc
change" + **rebuild-first from the base sha**). The rebuild-first discipline paid off again:
cold build from `6192ff1` was `cache get` ~2 min + `lake build bang` ~7 min (kernel cold-compile
is slower than the README's ~4 min estimate — worth noting the estimate is optimistic on a busy
machine), then all findings are against that freshly-built binary. Two round-3 additions worth
keeping:

1. **Probe one step past every example.** The three custom-effect examples are all single-op;
   the bug is exactly at op #2. The method's leverage is *varying the dimension the examples
   hold fixed* — a stranger writing their OWN effect naturally reaches for two operations, and
   that's where the surface breaks. "Try variations the docs imply should work" is where S1s live.
2. **Separate `run` from `check --json` on the SAME program** — they gave different error
   messages for the identical multi-op bug (`app: callee is not a function` vs `let-binding
   '#p': unbound variable n`), and the `check --json` path is where the span-null regression
   would hide. Diff the two diagnostic surfaces, don't trust one.

Round-3 template programs (all original): a self-authored `Log`/`Calc` multi-op effect battery,
a param-carrying `Cfg` probe, a keyword-clash op-name sweep, a `double`/`main` program driven
through all six `query` verbs + both `rewrite` verbs + the preservation-gate hazard, and the
`bang test` law workaround. Re-run at each ◊; the user-effect surface + the reusable-handler
story (#84) are the parts most likely to move.
