# PATH-inert-top-level-language-contract — make descriptions the default execution boundary

> Enforce ADR-0118 end to end: every ordinary top-level declaration is inert, entry `main` is the
> sole computed declaration, and the former strict-initializer divergence witness becomes a refusal.

## Seam

- **From checkpoint**: the constructor-aware contract probe priced Option A at exactly three
  non-`main` bindings (`nqueens.q4/q5/q6`) and proved the production enforcement phase.
- **To checkpoint**: valid libraries contain descriptions and suspended recursive definitions only;
  entry programs compute in `main` or their trailing body, with B019 guarding every frontend route.
- **Contract preserved**: the kernel, evaluator, constructor precedence, optional trailing-body entry,
  query schema, and body-artifact negative link flags are unchanged.

## Layer

- [ ] Kernel  [x] Compiler  [x] Surface language  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a language user and future link-tool author need one visible boundary between
  descriptions and execution, rather than source-order-dependent hidden work.
- **Public starting point**: write library values, thunks, and `let rec` definitions normally; put
  entry computation in `main` or in the trailing program body.
- **Terminal observation**: inert constructor values such as `Some(3)` check; `Some(1 + 2)` and
  `let eager = 1 + 2` fail with B019 naming the binding and teaching suspension or relocation.
  A computed entry `main` remains legal, while an imported library's `main` is qualified and refused.
- **Adverse / recovery route**: `--no-typecheck` cannot bypass source well-formedness; query dump keeps
  structural facts for a refused subject but nulls checked rows/core identity and carries B019 as the
  declaration `typeError`.
- **Downstream journey released**: initialization divergence no longer needs a link slot. Independent
  body typing, import-slot validation, runtime effect relocation, and the linker itself remain open.

## Feeds the constraint

- **Binding constraint now**: BANG's description-until-forced architecture needs top-level syntax to
  agree with the body-artifact boundary; implicit eager siblings made unreachable work observable.
- **How this path feeds it**: enforce the conservative inert whitelist after authoritative constructor
  resolution and before declaration folding, leaving only explicit entry computation observable.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| constructor syntax hides eager payload work | `Some(1 + 2)` A-normalizes eager work | high / high / low | **recurse through payloads and fail closed** | initializer classifier changes |
| a same-named binding spoofs constructor identity | elaboration resolves constructors before values | low / critical / low | **share the authoritative resolution rule and gate the pole** | name precedence changes |
| `main` is mistaken for a suffix convention | imported names are resolver-qualified | medium / high / medium | **exempt only bare entry `main`; library `Lib_main` is ordinary** | entry resolution changes |
| slice instrumentation becomes a language backdoor | fidelity harness needs a computed synthetic declaration | low / high / low | **reserve one tokenizer-hostile name beside the rule** | another internal consumer appears |
| pure constants become needlessly awkward | corpus has no library example, but future packages may | medium / medium / medium | **retain an explicit-init/memoizing-handler door; prebuild neither** | a program needs shared compute-once work |
| closing initialization is overclaimed as linking | independent typing/import slots/linker remain absent | high / critical / high | **keep `linkReady=false`** | complete link validation lands |

## Evidence

- The migrated 61-journey census is **233 manifest values + 24 recursive definitions + 14 computed
  `main`s = 271 occurrences**; no non-`main` computation remains.
- The old divergent sibling fixture is still counted by the hidden syntax census, then refused by
  B019 before checking or either evaluator. `tools/test-initializer-census.sh` explicitly pins
  `bang run --no-typecheck` to the same refusal. Query behavior is explicitly pinned.
- A valid divergent `main` keeps aggregate declaration rows chain-cumulative, preserving ADR-0117's
  warning that `DeclFact.row` is not initializer-local evidence.
- `examples/nqueens/main.bang` now computes q4/q5/q6 locally inside `main` and still returns `21004`.
- The slice-fidelity harness uses the shared unspellable internal-entry name; no user-spellable
  exemption or schema field was added.

## Plan

1. [x] Record the operator's Option A decision and its costs in ADR-0118.
2. [x] Enforce the constructor-aware inert whitelist and stable B019 before declaration folding.
3. [x] Migrate n-queens and convert the strict initializer witness to an expected refusal.
4. [x] Pin raw/query/slice behavior and retain a valid chain-cumulative-row pole through `main`.
5. [x] Regenerate the project map, pass full convergence, publish, and close advisor review.

## Status

- [x] Started 2026-07-19
- [ ] In flight
- [ ] Blockers: none
- [x] Completed 2026-07-19
- Convergence evidence: 1,456 Lean jobs; 33/33 batteries; query 292/292; initializer 31/31;
  rewrite 40/40; annotate 21/21; explain 26/26; fitness and full `just verify` green.
- Fable 5's read-only adversarial audit found no blocker. Its two should-fixes are closed here: the
  role-agnostic per-declaration projection is documented and gated, and this path cites the existing
  raw `--no-typecheck` B019 pole explicitly.
- Reopen / observe: reopen the conservative pure-computation restriction only when a real library
  journey needs compute-once work or source-safe totality/effect provenance becomes independently real.

## Owner

- Agent / human: Codex, with persistent Fable 5 advisor in Herdr `lang-bang`
