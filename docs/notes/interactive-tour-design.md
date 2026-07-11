<!-- note-status: active -->
# Interactive language tour + in-browser playground — design

**Status**: design probe (docs-only). Off main @ `16060b5f`, branch `design-interactive-tour`.
**Question**: how do we ship a Gleam/Elysia-class interactive tour — editable code, per-lesson
expected output, run-in-browser — for a language whose runner is a Lean 4 + Mathlib binary?

The surprise: **bang's no-ambient-IO v1 makes the server-backed door unusually cheap, and the
existing `examples/` corpus IS the lesson source** (drift-proof by the repo's own derivation
ladder). The client-side-wasm door (the Gleam outcome) is a hard non-starter today for a
Mathlib-linked Lean binary — quantified below.

---

## 1. How the reference-class tours execute code (census)

| Tour | Execution model | Where code runs | Infra cost |
|---|---|---|---|
| **Gleam tour** | compiler-as-wasm; compiles Gleam→JS **in the browser**, runs the JS; web-worker off UI thread; precompiled stdlib fetched on demand | client | static host only |
| **Rust playground** | server-backed: React FE → backend → **Docker** container per run (no network, cgroup mem/time limits) | server | container fleet |
| **Go tour** | server-backed sandboxed exec (`play.golang.org`) | server | server |
| **Elysia / TS docs** | code is JS/TS — **runs natively** in the page, no compile step | client | static host only |
| **Next.js Learn** | checkpointed lessons; **no in-browser exec** of the framework; outputs are authored/screenshotted | none | static host only |
| **SQLite / Postgres (pglite) playgrounds** | the **engine itself** compiled to wasm (C→wasm, mature toolchain) | client | static host only |

Friction ranking (lowest first): **native-JS** (Elysia) > **client-wasm** (Gleam, SQLite) >
**server-backed** (Rust, Go) > **no-exec** (Next). The client-wasm winners share one trait:
a *self-contained toolchain that already targets wasm well* (Rust-core→wasm; C→wasm). Lean is
not in that club yet (§2, door 1).

---

## 2. The bang feasibility fork — four doors, ground in the repo

The runner is `.lake/build/bin/bang` — `bang run <file.bang>` / `bang eval "<expr>"`, Lean 4 +
Mathlib, fuel-bounded (`Main.lean`: default fuel, `--engine=env|compiled|oracle`, `--fuel N`).

### Door 1 — client-side wasm compiler (the Gleam outcome). **VERDICT: non-starter in 2026.**
Ship the whole runner as browser wasm → full language, all effects, zero backend. This is what
Gleam does with a Rust compiler. For a **Lean 4 + Mathlib** binary the honest state (Lean Zulip
`wasm build`, corroborated by the FRO's own posture):

```
artifact size    wasm + glue.js = 100 MB (11 MB gzip);  .olean = 500 MB (190 MB gzip)
runtime          Node.js only — NOT browser-ready ("wasm thread semantics are web-specific")
stability        non-deterministic segfaults after ~2000 instructions under `lean --run`
Mathlib          not demonstrated; wasm "significantly complicates bootstrapping/plugin
                 situation for libraries like mathlib that depend on compiled tactics"
32-bit ABI       boxing/unboxing arithmetic overflow bugs
```

bang's binary is Mathlib-linked (EffRow is a `Finset`, the kernel rides Mathlib order/lattice
typeclasses). The exact thing the Lean wasm build can't yet do is the exact thing bang needs.
Even setting Mathlib aside, an 11 MB-gzip download that segfaults at 2000 instructions and
runs only under Node is not a browser tour. **Revisit when: FRO ships a browser-usable wasm
build AND Mathlib-linked code runs** — track, don't build.

### Door 2 — server-backed exec service (the Rust-playground pattern). **VERDICT: recommended v1.**
A tiny HTTP service wrapping the existing binary: `POST /run {source} → {stdout, exit, timedOut}`.
The Rust-playground shape (Docker-per-run, no network, cgroup mem+time caps) — but bang needs
**far less sandbox** than Rust, because of what v1 bang *cannot express*:

- **No filesystem effect, no network effect, no ambient IO** exist in the language (v1 effect
  set is pure/State/Choice/custom handlers; IO is a *mock handler*, `echo-mock`). A bang program
  cannot open a socket or read a file because there is no operation in the language to do so.
- **Fuel-bounded by construction** — `Source.eval` and `exec` both take a fuel ceiling; infinite
  loops terminate as a defined fail-loud value, not a hang. Wall-clock is a backstop, not the
  only guard.
- The **one real IO surface** is module resolution: `Main.lean`'s `resolveModulePath` /
  `containedRealPath` do `IO.FS.realPath` and a *contained-root* check. The service runs
  single-file (`bang run /sandbox/main.bang`, no imports) → this path is inert. If multi-file
  lessons are wanted later, the containment check already exists.

So the sandbox reduces to: **CPU-time cap + memory cap + no-fork + read-only FS + drop the
filesystem** (the binary needs only its own `.olean`s + the single input file). That is a
`systemd-run --scope -p MemoryMax -p CPUQuota` or a minimal seccomp/`bubblewrap` jail — *lighter
than Docker-per-run* because there's no untrusted-IO attack surface to contain. This is the
"unusually cheap because no ambient IO" path the probe anticipated, and it holds.

**Residual abuse surface** (real, but bounded): CPU exhaustion (→ CPUQuota + fuel), memory
(→ MemoryMax), fork-bomb (→ `pids-max=1`/no-new-privs), the `bang` process itself being a Lean
runtime with native libc (→ seccomp default-deny + non-root + read-only rootfs). No data
exfiltration vector exists in the language. Rate-limit at the edge for cost, not safety.

### Door 3 — rung-1 wasm (pure arithmetic → `.wat`). **VERDICT: not a tour engine; a demo later.**
`docs/notes/emission-rung1-probe.md`: only the **pure ⊥-row arithmetic fragment** compiles to
browser-runnable wasm today (4/4 == `Source.eval` on wasmtime). That's a genuine artifact but
covers ~1 of 10 planned lessons (no effects, no handlers, no data). Its place: a **"see the
compiled output"** panel on the arithmetic lessons — show the `.wat`, run it client-side — a
*complement* to door 2, not a replacement.

### Door 4 — no-exec, pre-recorded outputs (the Next-Learn fallback). **VERDICT: zero-infra floor.**
Checkpointed lessons; each shows source + its committed `expected.txt`; "run" reveals the stored
output (optionally an asciinema cast). **Loses**: the edit-and-see-it loop (the whole point of an
interactive tour). **Keeps**: correctness (outputs are the gated oracle) at zero backend cost —
deployable as pure static content on the existing `site/` GitHub Pages target *today*. This is
the honest **v0** that ships with the vocs site before any exec service exists, and the graceful
degradation when the service is down.

### The recommended ladder

```
  v0  (now)   no-exec, corpus-generated lessons + expected.txt  →  static, on the vocs site
  v1          + server-backed /run (door 2), light no-IO sandbox →  one small service
  v1.x        + "compiled output" wasm panel on arith lessons (door 3)
  post-v1     ⟶ client-side wasm (door 1) IFF Lean FRO ships browser+Mathlib wasm
```

Door 2 is the workhorse. Door 4 is its floor and fallback. Door 1 is a watch item, not a plan.

---

## 3. The no-IO sandboxing assessment (the potentially-cheap finding, quantified)

The claim "v1 bang barely needs sandboxing" is **true at the language level, with a caveat at the
process level**:

| Threat | Present in v1 bang? | Guard needed |
|---|---|---|
| File read/write from a program | **No** — no FS effect exists | none (language-level) |
| Network from a program | **No** — no net effect (IO is a mock handler) | none (language-level) |
| Infinite loop / non-termination | Bounded | fuel (built-in) + CPUQuota (backstop) |
| Memory blowup | Possible (big data values) | MemoryMax (cgroup) |
| Fork bomb | Via the *process*, not the language | `pids-max`, no-new-privs |
| Native-runtime escape (Lean/libc CVE) | The one genuine surface | seccomp default-deny, non-root, RO rootfs |

**Net**: the sandbox is a resource-limit jail, **not** a data-isolation jail — because there is
no data to isolate the program from. Concretely: `systemd-run --user --scope -p MemoryMax=256M
-p CPUQuota=50% -p TasksMax=8` around the binary, run as a nobody user in a read-only bind of
`.lake/build` + a tmpfs `/sandbox`, `--fuel` set modestly. Estimated build effort: **a few
hundred lines + a Dockerfile/systemd unit**, not the Rust-playground's container-orchestration
weight. This is the design's headline cheap win.

---

## 4. Lesson-generation pipeline — corpus → lessons, drift-proof

The repo already runs the top rung of the derivation ladder for run-outputs:
`examples/<name>/{main.bang, expected.txt, README.md}`, gated end-to-end by
`tools/check-examples.sh` (run every `main.bang`, diff stdout vs `expected.txt`; `--update NAME`
re-bakes one oracle as a reviewable git diff). **36 example projects** exist, each a pre-verified
`(program, expected-output)` pair. Plus a bang **TextMate grammar** generated from the parser
tables (`web/docs/bang.tmLanguage.json`, `tools/gen-tmgrammar.py`) already highlights ` ```bang `
fences in the vocs site — highlighting cannot drift from the parser.

**The pipeline** (a lesson's expected output IS its `expected.txt` — same SSoT move as the site):

```
examples/<name>/main.bang     ─┐
examples/<name>/expected.txt   ├─►  gen-lessons.(mjs|py)  ─►  site/tour/<nn>-<name>.mdx
examples/<name>/README.md     ─┘        (a generator)          (prose + <Lesson> component)
tools/check-examples.sh  ──────────────► already gates that expected.txt == actual output
```

- A lesson references its example by **path**, never copies the code or output (SSoT: the
  `main.bang` and `expected.txt` are the roots; the `.mdx` embeds them at build time).
- **Drift is caught by the existing gate**: if a lesson's shown output diverges from reality,
  `check-examples.sh` already fails in `just verify` — no new invariant to maintain. Add one
  thin check that every `site/tour/*.mdx` points at a real `examples/<name>/`.
- **Lesson prose** (the teaching text, one concept per page) is the *only* hand-authored part —
  it can't be generated, and shouldn't be. The code and output beneath it are generated.
- **Versioning**: lessons pin to the release binary (the `expected.txt` is valid for the binary
  that produced it); the tour build uses the same pinned `bang` the examples gate uses.

Where it lives: the operator ruled web/ bundling. The vocs `site/` already renders repo markdown
and highlights bang. **Recommend `site/tour/`** as a vocs section (generated `.mdx`), with the
`<Lesson>` editor component POSTing to the door-2 `/run` service. This reuses the one static
site + one grammar + one deploy; the tour is a *section*, not a second web property.

---

## 5. First 10 lessons (mining the corpus A-series)

One concept per page (Gleam precedent). Each row = an existing gated example → its lesson.

| # | Lesson | Seed example | Teaches | expected |
|---|---|---|---|---|
| 1 | Values are thunks; `$` forces | `effect-op-arith` (arith line) | description-vs-value, `$` (ADR-0007) | 70 |
| 2 | Functions & recursion | `tokenizer` / `nqueens` | structural recursion, the pure fragment | 3 / 21004 |
| 3 | Your own data | `derive-eq-ord` | `data`, constructors, pattern match | — |
| 4 | Strings & the stdlib | `string-stdlib` | injected `concat`/`reverse`/`eq` | 1 |
| 5 | State as a *library* | `state` | State is a handler, not a keyword | 5 |
| 6 | Handling an effect | `handle` | `with`, catching `raise` | 7 |
| 7 | Declare your own effect | `handle-custom-tracer` | `effect` decl, perform, handle e2e (ADR-0095) | 30 |
| 8 | Swap the handler, keep the program | `logger-silent` / `logger-counting` | same program, two handlers → 0 / 3 | 0 / 3 |
| 9 | Identity dispatch (the lexical cap) | `handle-custom-nested` | why `210` not `30` (ADR-0055) | 210 |
| 10 | Generation as an effect | `gen-seed-a` / `gen-seed-b` | seeded replayable runs — the DST warm-up | 6 / 15 |

The **moat lessons** (7–10: effects, handler-swap, identity dispatch, effect-as-value) are what
distinguishes bang from Elysia/Gleam — lead the tour toward them. A later B-series mines
`json` (multi-file modules), `calc` (the 6-module dogfood), `parser-combinators` (polymorphism),
`ndet-replicated-kv-*` (the CALM claim in miniature).

---

## 6. Cost estimates per door

| Door | Build effort | Ongoing cost | Abuse surface |
|---|---|---|---|
| 4 no-exec (v0) | small (generator + `<Lesson>` static component) | **$0** (static host) | none |
| 2 server-backed (v1) | small–medium (`/run` service + light jail + FE editor) | one small VM/container; rate-limited | resource-only (§3) |
| 3 wasm arith panel | small (reuse `WasmEmit` + wasmtime-in-browser) | $0 (static) | none (pure fragment) |
| 1 client wasm | **blocked** (upstream Lean FRO work) | $0 if it ever lands | none |

The whole v0→v1 is *small-to-medium* precisely because doors 4 and 2 both reuse existing
gated artifacts (corpus, grammar, binary) and the no-IO property collapses the sandbox.

---

## 7. Proposed issues (do not file)

1. **`site/tour/` scaffold + `<Lesson>` component** (door 4, v0) — generated `.mdx` from
   `examples/`, static "reveal expected output", ships on the current vocs deploy.
2. **`gen-lessons` generator + drift check** — `examples/<name>` → `.mdx`; a `just` gate that
   every `site/tour/*.mdx` references a real example (rides `check-examples.sh` for output truth).
3. **`bang serve` / `bang-play` exec service** (door 2, v1) — `POST /run`, light no-IO jail
   (`systemd-run` scope, MemoryMax/CPUQuota/TasksMax, seccomp, non-root, RO rootfs, `--fuel`).
4. **Wire the editor to `/run`** — the `<Lesson>` component gains an editable buffer + Run button.
5. **Arith "compiled output" panel** (door 3) — reuse `Bang/Backend/WasmEmit.lean` +
   wasmtime-in-browser for lessons 1–2.
6. **Watch item**: Lean-FRO browser+Mathlib wasm — revisit door 1 when it lands (no work now).

---

## Report summary

- **Door verdict**: **server-backed (door 2) for v1**, on a **no-exec corpus-generated floor
  (door 4) shippable now**; client-wasm (door 1) is a watch-item, not a plan.
- **Sandboxing finding**: v1 bang needs a *resource-limit* jail, **not** a data-isolation one —
  no FS/net/ambient-IO effect exists in the language, and it's fuel-bounded. `systemd-run` scope
  + seccomp + non-root RO-rootfs suffices; lighter than Rust's Docker-per-run.
- **Lean-to-wasm honest state (2026)**: Node-only, not browser-ready; 11 MB-gzip wasm + 190 MB-gzip
  `.olean`; segfaults ~2000 instructions; **Mathlib-linked code not supported** (the exact
  blocker for bang's binary). Non-starter for a browser tour today.
- **Lesson pipeline**: the 36-example `examples/<name>/{main.bang,expected.txt}` corpus + the
  parser-derived TextMate grammar are the drift-proof seed — a lesson's expected output IS its
  gated `expected.txt`; `check-examples.sh` already enforces the truth.
