# BANG resource-contract journey — docs-first participant report

Session workspace: `/tmp/bang-session-docs-first`

Product tree consulted read-only: `/tmp/lang-bang-rebase.HtbDJs`

Counting convention: an action is one document/example consultation, CLI invocation, or emitted-artifact inspection. Creating/copying disposable source and transcribing already-observed evidence are not product-facing actions. A combined shell command containing multiple CLI invocations counts each invocation. No task approached the 20-action stop limit.

## T01 — Orient

Outcome: PASS. In my own words, BANG is trying to let a program state semantic interfaces/laws, effect permissions, and local value-use obligations independently from the runtime handlers that realize them, while preserving those descriptions through checking and compilation. The smallest directly signposted example combining a semantic contract and a local resource obligation is `examples/resource-contract/`: `Permit.bang` declares the `Permit` effect, `preserves_zero` law, and `Identity`/`Negate` realizations; `main.bang` adds `use [1] permit` and `use [0] ghost`.

First-attempt status: PASS; the public language reference directly named the example.

Counts: 5 actions, 0 errors, 0 detours.

Oracle evidence:

- `docs/reference/language.md` says `use [q]` is separate from effect rows, defines `[0]`, `[1]`, and `[omega]`, and links `examples/resource-contract/`.
- `examples/resource-contract/Permit.bang` contains the effect, one law, and two handlers.
- `examples/resource-contract/main.bang` contains both local obligations and selects `Identity`.
- `examples/resource-contract/expected.txt` contains `7`.

Task trace:

1. Created the fresh workspace and consulted `README.md`. Learned the description/thunk/force model, handler-as-runtime-policy thesis, three engines, and built binary path. Assumption formed: semantic descriptions and realizations are intended to remain separately inspectable.
2. Consulted `ONBOARDING.md`. Learned the roles of `check --json`, `query dump`, and the three engines. No command was copied blindly because the packet required the already-built product.
3. Consulted `docs/reference/language.md` lines 1–360. Found traits/laws, user effects, handlers, `pledge`, and `use [q]` surface forms.
4. Consulted `docs/reference/language.md` lines 360–760. Found the exact resource semantics and direct `examples/resource-contract/` pointer.
5. Read all four files in `examples/resource-contract/`. Identified it as the requested smallest example.

## T02 — Establish the example's evidence

Outcome: PASS. The checked entry point evaluates to `7` on all three engines. Both alternative realizations pass the shared law over 30 deterministic samples. `query contract` returns a single JSON object joining contracts, realizations, quantities, law instances, and compiler evidence.

First-attempt status: PASS; all CLI invocations succeeded on first use.

Counts: 7 actions, 0 errors, 0 detours.

Oracle evidence:

```text
bang check --json examples/resource-contract/main.bang
{"ok":true,"diagnostics":[]}

bang run --engine=env examples/resource-contract/main.bang
7
bang run --engine=oracle examples/resource-contract/main.bang
7
bang run --engine=compiled examples/resource-contract/main.bang
7

bang test examples/resource-contract/Permit.bang
✓ Permit@Identity.preserves_zero — PASS (30 samples)
✓ Permit@Negate.preserves_zero — PASS (30 samples)
laws: 2/2 passed
```

The joined response had top-level `ok:true`; a `Permit_Permit` contract with `spend` and `preserves_zero`; two realizations; `ghost` declared/observed `[0]`; `permit` declared/observed `[1]`; two concrete law instances; and evidence `{typeChecked:true, quantityChecking:"exact-local", quantityErasure:"before-lowering", backendErasure:"manifest-unused-let-result"}`. Full raw response: `T02-evidence.txt`.

Task trace:

6. Ran `bang --help`. Located exact syntax and exit contracts for `check`, `test`, `query contract`, `emit`, and `explain`; noted that query-operation success and answer validity are different concepts.
7. Ran `check --json`; it returned `ok:true` with no diagnostics.
8. Ran the `env` engine; output `7`.
9. Ran the `oracle` engine; output `7`.
10. Ran the `compiled` engine; output `7`.
11. Ran `test` on the decls-only `Permit.bang`; both law instances passed 30 samples and the summary was `2/2 passed`.
12. Ran `query contract` on the entry point; received the joined JSON described above.
13. Preserved all outputs verbatim in `T02-evidence.txt`.

## T03 — Make and recover from a realistic mistake

Outcome: PASS. Duplicating the spend under `use [1] permit` produced B018: the body was observed as `[omega]`. Public `bang explain B018` said sequential uses add and saturate at omega and offered widening to `[omega]`. Keeping both calls and changing only the assertion to `[omega]` type-checked and ran to `15`.

First-attempt status: PASS for the intended journey: the invalid version was rejected on its first check and the help-directed recovery succeeded on its first attempt.

Counts: 4 actions, 1 expected program error, 0 detours.

Oracle evidence:

```json
{"ok":false,"diagnostics":[{"severity":"error","code":"type","explainCode":"B018","msg":"quantity mismatch: 'use [1] permit' requires [1], but the body has [omega]","span":null}]}
```

`bang explain B018` explicitly said: `[1]` requires one use on every alternative path; sequential uses add and saturate at `omega`; remove the duplicate/forgotten use or widen to `[omega]`. The recovered check returned `{"ok":true,"diagnostics":[]}` and run printed `15`.

What the diagnosis taught me: quantities track local value usage, not dynamic effect counts or row weights. Two sequential syntactic uses cannot satisfy exact-one; the system conservatively represents the duplicate as unrestricted/omega.

Task trace:

14. Created disposable `Permit.bang` and `main-invalid.bang`; only the latter differed semantically, with `permit.spend(7) + permit.spend(8)` still under `[1]`.
15. Checked the invalid version. Exit 1; received B018 and observed `[omega]` versus required `[1]`.
16. Ran only public help, `bang explain B018`. It provided the precise recovery while keeping both calls: widen to `[omega]`.
17. Created `main-recovered.bang` with both calls unchanged and only `[1]` changed to `[omega]`.
18. Checked the recovered version. Exit 0; `ok:true` and no diagnostics.
19. Ran the recovered version. Exit 0; output `15`.
20. Preserved the invalid diagnostic, teaching text, recovery, accepted check, and result in `T03-evidence.txt`.

## T04 — Transfer the semantic model

Outcome: PASS. Swapping the installed realization from `Identity` to `Negate` without changing the shared computation changed the result from `7` to `-7`; all three engines agreed. Both shared law instances still passed, and quantity/compiler evidence was unchanged.

First-attempt status: PASS; both pre-run predictions were correct.

Counts: 6 actions, 0 errors, 0 detours.

Pre-run prediction: output `-7`, because `Negate.spend(n)` is `0 - n`; law still holds, because `0 - 0 == 0`.

Oracle evidence:

```text
bang check --json main-negate.bang
{"ok":true,"diagnostics":[]}

env:      -7
oracle:   -7
compiled: -7

✓ Permit@Identity.preserves_zero — PASS (30 samples)
✓ Permit@Negate.preserves_zero — PASS (30 samples)
laws: 2/2 passed
```

Before/after comparison:

- Observable result: `7` → `-7`.
- Engine agreement: 3/3 before and 3/3 after.
- Type validity: true before and after.
- Quantities: `ghost [0]/[0]`, `permit [1]/[1]` before and after.
- Laws: both realizations passed before and after.
- Joined realization naming changed with import selection: selected `Identity` was unqualified before and selected `Negate` was unqualified after; the unselected sibling was module-qualified.

Task trace:

21. Stated prediction before editing/running.
22. Created `main-negate.bang`, changing only the imported/installed handler names.
23. Checked it; valid with no diagnostics.
24. Ran `env`; `-7`.
25. Ran `oracle`; `-7`.
26. Ran `compiled`; `-7`.
27. Re-ran `test Permit.bang`; both laws passed 30 samples.
28. Queried the joined contract view; quantities and compiler evidence matched T02, while selected-realization qualification changed.
29. Preserved prediction, output, query, and comparison in `T04-evidence.txt`.

## T05 — Inspect a concrete compilation consequence

Outcome: PASS after one inspection detour. The emitted WAT constructs the unused `99` and immediately drops it, but never puts that value in an `$env` cell.

First-attempt status: PARTIAL. Emission succeeded first attempt; an initially malformed regex delayed the environment-cell search by one command.

Counts: 4 actions, 1 command/search error, 1 detour with successful recovery.

Oracle evidence from generated `resource-contract.wat`:

```wat
377  (func $_start (export "_start") ...
378    (local.set 0 (ref.null $env))
379    (call $render
380    (block (result (ref null $val))
381    (drop (struct.new $ival (i64.const 99)))
382    (block (result (ref null $val))
383    (local.set 1 (struct.new $env (struct.new $ival (i64.const 0)) (local.get 0)))
```

The unique `i64.const 99` occurrence is inside `drop(struct.new ...)`: its binding expression is emitted/executed and its result discarded. A fixed-string search found all `$env` constructions at lines 375, 383, 385, and 386; none contains `99`. Therefore no runtime environment cell is retained for `ghost`.

Task trace:

30. Ran `bang emit ... -o /tmp/bang-session-docs-first/resource-contract.wat`. Exit 0, empty stdout, 395-line artifact produced.
31. Inspected the artifact header and first 280 lines to understand `$val`, `$ival`, and `$env`; no conclusion yet, then moved to `_start` where program-specific code resides.
32. Inspected lines 320–395 and searched for `99`; found the decisive line 381. The same compound inspection attempted a regex for `$env`, but escaping produced `rg: regex parse error ... unclosed group`. This was a tooling detour, not a product failure.
33. Recovered with `rg -n -F 'struct.new $env'`; obtained the four environment constructions and verified none stores `99`.
34. Preserved the excerpt, failed search, recovery, and interpretation in `T05-evidence.txt`.

## T06 — Judge machine-readable invalidity

Outcome: PASS. A naive consumer could mistake query-operation success for program validity: the invalid twice-used program produced process exit 0 and top-level `"ok":true`. The safest validity signal is `evidence.typeChecked`, which is explicitly false; `evidence.error` supplies the reason.

First-attempt status: PASS; the first joined query exposed the ambiguity and dedicated validity field.

Counts: 1 action, 0 errors, 0 detours.

Oracle evidence:

```json
{
  "ok": true,
  "quantities": [
    {"name":"ghost","declared":"[0]","observed":"[0]"},
    {"name":"permit","declared":"[1]","observed":"[omega]"}
  ],
  "evidence": {
    "typeChecked": false,
    "error": "quantity mismatch: 'use [1] permit' requires [1], but the body has [omega]"
  }
}
```

The command exited 0. Consumers should gate validity on `evidence.typeChecked === true`, not process exit, top-level `ok`, presence of contracts/laws, or a home-grown comparison of quantity strings.

Task trace:

35. Ran `bang query contract main-invalid.bang`. Exit 0; response retained contracts, realizations, quantities, and laws; top-level `ok:true`; nested `evidence.typeChecked:false` and explicit error.
36. Preserved the complete raw response and judgment in `T06-evidence.txt`.

## Severity-ranked findings

### 1. High — joined-query operation success is easy to confuse with program validity

Observation: On the invalid source, `query contract` exits 0 and returns top-level `ok:true`, while only nested `evidence.typeChecked:false` marks invalidity.

Interpretation: Automation that applies the conventional `exit == 0 && ok == true` gate will accept an invalid program. The dedicated nested field is safe once known, but the top-level shape invites the wrong default.

Alternative explanation: CLI help documents that query exit status represents whether the query operation ran, not necessarily whether its answer is positive. That design is internally consistent; the concern is discoverability and schema ergonomics for naive consumers.

### 2. Medium — realization identifiers in joined output change qualification when selection changes

Observation: With `Identity` imported, the joined view names it `Identity` and the sibling `Permit_Negate`; after swapping the import it names the selected one `Negate` and the sibling `Permit_Identity`.

Interpretation: A machine consumer diffing semantic identities may see unnecessary identifier churn or need import-aware normalization.

Alternative explanation: These may intentionally be elaborated in-scope names rather than stable globally qualified IDs, and the contract links remain intact.

### 3. Low — proving dead-cell omission from WAT requires structural inference

Observation: The artifact clearly emits `(drop (struct.new $ival (i64.const 99)))` and no `$env` construction containing `99`, but it contains no source name/comment tying that code to `ghost`.

Interpretation: The consequence is inspectable, but a less distinctive binding expression would make manual attribution harder.

Alternative explanation: Minimal WAT output may be intentional, and `query contract` already provides the higher-level `manifest-unused-let-result` evidence label; source maps/comments are not necessary for execution.

### 4. Positive — B018 diagnosis and public recovery are unusually actionable

Observation: The check response gives stable code B018, declared and observed quantities, and `bang explain B018` directly offers the `[omega]` recovery while explaining sequential saturation.

Interpretation: A first-time functional programmer can recover without internal docs or hints.

Alternative explanation: None observed in this journey; the only caveat is the multi-file diagnostic's documented null span.

### 5. Positive — the public example supports a complete evidence loop

Observation: One small example supported checking, three-engine execution, cross-realization law testing, joined JSON inspection, controlled realization swap, invalidity inspection, and concrete emission.

Interpretation: The documentation successfully transfers BANG's central separation between semantic contract, runtime realization, effect row, and local quantity.

Alternative explanation: The example README states expected outcomes, so prediction tasks are partly pre-answered if it is read during orientation; the actual commands independently confirmed them.

## Artifact inventory

- `Permit.bang` — disposable public contract copy.
- `main-invalid.bang` — duplicate use under `[1]`.
- `main-recovered.bang` — both calls retained under `[omega]`.
- `main-negate.bang` — unchanged computation with `Negate` installed.
- `T02-evidence.txt`, `T03-evidence.txt`, `T04-evidence.txt`, `T05-evidence.txt`, `T06-evidence.txt` — preserved raw evidence.
- `resource-contract.wat` — emitted compiler artifact.
- `end-session-report.md` — this report.

No product-tree files were edited. No forbidden source, score key, internal implementation, git history, project-management material, or another session's artifacts were consulted.
