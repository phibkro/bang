# PATH-compiled-browser-demo-pack — ship honest compiled BANG programs in a browser

> Turn the existing rung-5 emitter into a public, reproducible browser journey without implying a
> source playground, broad WASI support, or a stronger proof boundary than the project has earned.

## Seam

- **From checkpoint**: ◊5.5 emits real WasmGC+exception-handling modules and diffs them on engine
  batteries, but no maintained public browser journey executes those artifacts.
- **To checkpoint**: ◊5.75 publishes a small compiled-demo page whose committed modules execute in a
  real browser and byte-match the same example oracles used by the repository.
- **Contract preserved**: source semantics, emitter output, example oracles, capability authority,
  proof claims, and the explicitly deferred organic-validation loop remain unchanged.

## Layer

- [ ] Kernel  [x] Compiler artifact boundary  [x] Surface  [x] Meta (docs/process)

## Actor journey / observable outcome

- **Actor / need**: a curious visitor needs to see non-trivial BANG programs execute as compiled Wasm
  without installing Lean, Nix, or the compiler.
- **Public starting point**: the maintained “Compiled browser demos” documentation page.
- **Terminal observation**: choosing JSON, calculator, N-Queens, or either sim-KV realization runs a
  committed `.wasm` module locally in the browser and reports an exact oracle match.
- **Adverse / recovery route**: an unsupported browser, missing artifact, unexpected import/file
  descriptor, trap, or output mismatch is shown as a refusal/error rather than a successful result.
- **Downstream journey released**: this journey.

## Feeds the constraint

- **Binding constraint now**: `ROADMAP.md` ◊5.75 requires JSON and sim-KV browser execution with
  artifacts diffed against the kernel oracle; the site currently offers no executable demo boundary.
- **How this path feeds it**: publish the already-emitted artifact stratum with exact source/artifact
  provenance and enroll its Node differential in `verify` plus its real-browser journey in the site gate.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| “browser support” overclaims compatibility | first public demo; kill shot covers Chromium 150 only | high / medium / medium | name exact tested engines/date and fail visibly elsewhere | second browser engine is enrolled |
| committed Wasm drifts from sources/oracles | any compiler/example edit after this path | high / high / medium | generator records source hashes; verify checks artifact hashes and live oracle output | artifact schema changes |
| tiny shim is mistaken for WASI/host IO | modules import only `fd_write`; real host authority is a separate route | high / high / high | expose stdout-only contract; reject other imports/descriptors; publish refusal list | a demo requires an additional host capability |
| a demo is mistaken for a source playground | browser receives precompiled modules, not a compiler | high / medium / medium | label precompiled boundary in page and UI; no editor or arbitrary source input | a compiler-sized browser artifact is pulled by use |
| static route disappears under site derivation/base path | `web/docs/public` is generated and ignored | medium / high / medium | keep tracked inputs under `web/docs/static`; copy during sync; smoke deployed base-path assets | Vocs asset pipeline changes |
| output agreement is mistaken for a universal proof | current emitter evidence is rung/corpus scoped | medium / critical / high | say byte differential and tested stratum; make no semantic-proof claim | a verified emitter theorem covers this route |
| xv6/ambient IO gets green-stubbed | ROADMAP says xv6 waits on real FFI/IO design | medium / high / high | refuse ambient host IO and retain xv6 successor explicitly | the real IO authority contract lands |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: the docs offer prose about compilation, but no maintained route runs a
  BANG-emitted module in a browser.
- **Smallest tracer bullet**: publish five fixed artifacts behind one stdout-only runtime and compare
  each output to its committed `examples/*/expected.txt` oracle.
- **Positive evidence**: Node executes every committed artifact in `just verify`; the production-site
  smoke opens the page in headless Chromium and observes exact matches for every manifest entry.
- **Negative or recovery evidence**: the runtime rejects an unexpected import and non-stdout/stderr
  descriptor; the verifier falsifies a tampered artifact/hash/output in isolated copies.
- **Broader convergence gate**: `just test-compiled-browser-demo`, `just site-build`, `just fitness`,
  and `just verify`.
- **Assumptions / exclusions**: this establishes the named artifact corpus on the recorded engines. It
  does not establish arbitrary source compilation, all browsers, ambient host IO, performance, artifact
  independent typing/link safety, or universal compiler correctness.

## Plan

1. [x] Kill-shot current emitted JSON/calc/N-Queens/sim-KV modules in Node and Chromium.
2. [x] Add deterministic artifact generation, provenance, and a shared narrow runtime.
3. [x] Publish the docs + static runner through the base-path-aware site pipeline.
4. [x] Enroll differential, refusal, deployment, and real-browser gates; run full convergence review.

## Status

- [x] Started 2026-07-19
- [ ] In flight: none — the checkpoint is banked
- [ ] Blockers: none
- [x] Completed 2026-07-19
- Convergence evidence: `just test-compiled-browser-demo` passes 44 assertions; production-equivalent
  `just site-build` serves 279 routes under `/bang` and runs all five modules in Chromium; `just fitness`
  and full `just verify` pass with 34/34 batteries; Fable 5 independently reviewed the staged boundary
  and returned **ACCEPT** with no actionable findings.
- Retained failed gates / successors: arbitrary source playground and xv6/ambient IO remain outside the
  demonstrated stratum.
- Reopen / observe: expand only when a real demo pulls another host capability or a second browser is
  enrolled; run the already-required organic public journey before ◊6/release.

## Owner

- Agent / human: Codex, with read-only Fable 5 advisor

## Notes

The 2026-07-19 kill shot used Node 22.20.0 and Chromium 150.0.7871.124. All five modules executed
unchanged after `bang emit` + `wasm-tools parse` and produced `30163`, `11021193`, `21004`, `1120`, and
`1100` respectively (including their committed trailing newlines).
