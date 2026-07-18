# BANG resource-contract usability session — help-first participant

Session workspace: `/tmp/bang-session-help-first`

Product tree (read-only): `/tmp/lang-bang-rebase.HtbDJs`

Counting convention: an **action** below is a BANG CLI invocation, matching the packet's
"product-facing action" limit. Document reads, local file edits, and artifact inspection commands
are present in the chronological trace but not counted as product-facing actions. An **error
outcome** is a product invocation returning nonzero; expected invalid-program diagnoses are labeled
separately from unexpected errors. A **detour** is an abandoned/revised route rather than a normal
evidence-gathering step.

## T01 — Orient

- **Outcome:** Success. In my own words, BANG aims to let a program state semantic descriptions
  separately from execution choices: computations are explicitly observed; named effects declare
  operations and laws; handlers are swappable realizations; local quantities state value-use
  obligations; and the compiler carries/checks those descriptions while lowering to WebAssembly.
  The smallest permitted example combining a semantic contract and a local resource obligation is
  `examples/resource-contract/`: `Permit.bang` declares `Permit.spend`, the `preserves_zero` law,
  and `Identity`/`Negate`; `main.bang` adds `[0] ghost` and `[1] permit` obligations.
- **First-attempt status:** Yes.
- **Counts:** 1 product action; 0 error outcomes; 0 detours.
- **Oracle evidence:** `README.md`; `examples/resource-contract/README.md`, `Permit.bang`, and
  `main.bang`; `bang --help` exit 0.
- **Trace:** Chronology entries 01–06 below.

## T02 — Establish the example's evidence

- **Outcome:** Success. The checked program evaluates to `7`. `Identity` and `Negate` each pass
  `preserves_zero` for 30 samples (2/2). `query contract` returns one joined JSON object containing
  `contracts`, `realizations`, `quantities`, `laws`, and `evidence`. Its quantity facts say `ghost`
  is declared/observed `[0]` and `permit` `[1]`; its compiler evidence says `typeChecked:true`,
  exact-local checking, pre-lowering quantity erasure, and manifest unused-let-result backend
  erasure.
- **First-attempt status:** Yes.
- **Counts:** 4 product actions; 0 error outcomes; 0 detours.
- **Oracle evidence:** `evidence-t02.txt` (exact outputs); baseline source in
  `main.baseline.bang`/`Permit.bang`.
- **Trace:** Chronology entries 07–11.

## T03 — Make and recover from a realistic mistake

- **Outcome:** Success after one detour. The twice-used version promised `[1]` but was observed as
  `[omega]`; `check --json` returned exit 1 with `explainCode:"B018"`. `bang explain B018` says
  sequential uses add and saturate at omega and recommends widening to `[omega]` if both uses must
  remain. My first twice-use expression nested one effectful computation where a value was required;
  after widening, that independent error became visible (`not a value`). A permitted public-reference
  example showed two capability calls combined with `+`, so I used
  `permit.spend(7) + permit.spend(0)` in both invalid and recovered variants. Changing only `[1]` to
  `[omega]` then produced `{"ok":true,"diagnostics":[]}`, exit 0, and the retained two uses ran to
  `7`.
- **What the diagnosis taught me:** `[1]` means exactly one free use on every alternative path;
  multiple sequential uses are conservatively/unrestrictedly graded `[omega]`. Quantity is a local
  value-use axis, separate from the effect row. Widening the obligation asserts the actual use; it
  does not remove either operation.
- **First-attempt status:** No for the task as a whole: the intended B018 diagnosis succeeded on the
  first invalid check, but the first recovery exposed the independent nested-computation error.
- **Counts:** 6 product actions; 3 error outcomes (2 intended invalid checks, 1 unexpected failed
  recovery); 1 detour.
- **Oracle evidence:** `main.invalid.bang`, `main.recovered.bang`, and `evidence-t03.txt`.
- **Trace:** Chronology entries 12–23.

## T04 — Transfer the semantic model

- **Outcome:** Success. Before running I predicted `-7`, because only installation changes from
  `Identity` (`n`) to `Negate` (`0 - n`), while the shared computation still spends `7`. I predicted
  the law would continue to pass because negated zero is zero. Actual run: `-7`, exit 0; actual law
  suite: 2/2 passed. Before/after contract cards retain the same conceptual contract, two
  realizations, `[0]`/`[1]` quantities, two law instances, and `typeChecked:true`. The card's concrete
  names do flip qualification according to which realization is selected: baseline has `Identity`
  and `Permit_Negate`; swapped has `Permit_Identity` and `Negate`.
- **First-attempt status:** Yes; prediction matched.
- **Counts:** 4 product actions; 0 error outcomes; 0 detours.
- **Oracle evidence:** `main.swapped.bang`, `evidence-t04.txt`, compared with `evidence-t02.txt`.
- **Trace:** Chronology entries 24–29.

## T05 — Inspect a concrete compilation consequence

- **Outcome:** Success. In emitted `baseline.wat`, `_start` contains
  `(drop (struct.new $ival (i64.const 99)))`: the right-hand-side value is concretely constructed,
  so the binding expression still runs, then its result is discarded. An exact search finds no
  `struct.new $env` containing `i64.const 99`; the following environment cell instead contains `0`
  for handler machinery. Therefore no runtime environment cell is retained for `ghost`.
- **First-attempt status:** Yes.
- **Counts:** 1 product action; 0 error outcomes; 0 detours.
- **Oracle evidence:** `baseline.wat` lines 377–395, especially line 381; `evidence-t05.txt` records
  the excerpt and the no-match search.
- **Trace:** Chronology entries 30–34.

## T06 — Judge machine-readable invalidity

- **Outcome:** Success. Yes, a naive automation consumer can mistake query success for program
  validity: the invalid twice-used program returns process exit 0 and top-level `"ok":true`.
  The safest validity signal in this response is `evidence.typeChecked`, which is `false`;
  `evidence.error` corroborates it, as do quantity facts `declared:"[1]"` and
  `observed:"[omega]"`. Here, top-level `ok` and exit status mean the query operation ran, not that
  its subject type-checks.
- **First-attempt status:** Yes.
- **Counts:** 1 product action; 0 error outcomes; 0 detours.
- **Oracle evidence:** `evidence-t06.txt` contains the complete response and exit.
- **Trace:** Chronology entries 35–38.

## Complete chronological trace

01. Read `/tmp/bang-resource-contract-task-packet.md` with
    `sed -n '1,240p'`. Assumed the packet's allowlist is exhaustive and did not follow README links
    into forbidden/internal material. Did not read the score key.
02. Created the fresh workspace after asserting it did not exist:
    `test ! -e /tmp/bang-session-help-first && mkdir /tmp/bang-session-help-first && pwd`.
    Exit 0. All subsequent edits/generated artifacts stayed there.
03. Read permitted root `README.md` with `sed -n '1,260p'`. Relevant observations: BANG calls itself
    a language of semantic descriptions; computations/effects/resource obligations are independent
    of realization; `.lake/build/bin/bang` is the built binary path; `bang --help` is the command
    discovery entry point.
04. Searched only permitted surfaces:
    `rg -n -i "contract|permit|resource|obligation|realization|law" examples docs/reference/language.md ONBOARDING.md`.
    The results named `examples/resource-contract/` as the exact joined contract/resource example.
    This consulted matched snippets from `ONBOARDING.md`, `docs/reference/language.md`, and permitted
    `examples/**`; no forbidden result was opened (the resource README's mention of `scratch/` was
    not followed).
05. Read `examples/resource-contract/README.md`, `Permit.bang`, and `main.bang` with bounded `sed`.
    Assumption formed: expected result 7, two passing law instances, `[0] ghost`, `[1] permit`.
06. Ran `./.lake/build/bin/bang --help`; exit 0. Relevant discovery: `check --json`, `test`,
    `query contract`, `emit`, `explain CODE`, and explicit exit contracts.
07. T02 action 1: `bang check examples/resource-contract/main.bang` -> `ok`, exit 0.
08. T02 action 2: `bang run examples/resource-contract/main.bang` -> `7`, exit 0.
09. T02 action 3: `bang test examples/resource-contract/Permit.bang` ->
    `Permit@Identity.preserves_zero` PASS (30), `Permit@Negate.preserves_zero` PASS (30), 2/2, exit 0.
10. T02 action 4: `bang query contract examples/resource-contract/main.bang` -> complete JSON in
    `evidence-t02.txt`, top-level `ok:true`, `schemaVersion:1`, and all five requested categories;
    exit 0.
11. Used `apply_patch` to create workspace copies `Permit.bang`, `main.baseline.bang`, and
    `evidence-t02.txt`. Product tree remained untouched.
12. Used `apply_patch` to create initial `main.invalid.bang`, promising `[1]` around two nested
    `permit.spend` calls.
13. T03 action 1: `bang check --json main.invalid.bang` -> exit 1, B018 quantity mismatch,
    declared `[1]`, body `[omega]`. This was the intended refusal, not a detour.
14. T03 action 2: `bang explain B018` -> exit 0. Public help explained exact branch/sequential-use
    semantics and recommended `[omega]` when retaining duplicates.
15. Used `apply_patch` to create `main.recovered.bang` with `[omega]` and preserve initial evidence.
16. T03 action 3: `bang check --json main.recovered.bang` -> exit 1,
    `not a value (wrap a computation in braces)`. Unexpected error: after the quantity mismatch was
    fixed, nesting an effectful computation as `spend`'s value argument was independently invalid.
17. Read only the relevant permitted language-reference lines 390–430. They confirm `[omega]` is
    valid/unrestricted, so the quantity spelling was not the cause.
18. Searched permitted examples/reference for repeated effect-call syntax:
    `rg -n "use \\[omega\\]|\\$.*\\..*\\$|let .*\\{.*\\..*\\}" examples docs/reference/language.md | head -80`.
    Runnable public examples at language-reference lines 795/799 combine two calls using `+`.
19. Recovery: used `apply_patch` to revise both variants to
    `permit.spend(7) + permit.spend(0)`, leaving invalid/recovered files different only in
    `[1]` versus `[omega]`.
20. T03 action 4: rechecked `main.invalid.bang` -> same B018 mismatch, exit 1, now without the nested
    expression confounder.
21. T03 action 5: checked `main.recovered.bang` -> `{"ok":true,"diagnostics":[]}`, exit 0.
22. T03 action 6: ran `main.recovered.bang` -> `7`, exit 0. Both permit calls remain.
23. Used `apply_patch` to preserve all T03 outputs in `evidence-t03.txt`.
24. Predicted swapped result/law, then used `apply_patch` to create `main.swapped.bang`, changing
    both the import selection and installed handler from `Identity` to `Negate`, not the shared body.
25. T04 action 1: `bang check --json main.swapped.bang` -> ok true, exit 0.
26. T04 action 2: `bang run main.swapped.bang` -> `-7`, exit 0; prediction confirmed.
27. T04 action 3: `bang test Permit.bang` -> both realization law instances PASS (30 each), 2/2,
    exit 0; law prediction confirmed.
28. T04 action 4: `bang query contract main.swapped.bang` -> complete JSON, typeChecked true, exit 0.
    Compared against entry 10; semantic categories/quantities remain, observable result changes, and
    selected/unselected realization name qualification flips.
29. Used `apply_patch` to preserve prediction and outputs in `evidence-t04.txt`.
30. T05 action 1: `bang emit main.baseline.bang -o baseline.wat` -> exit 0; artifact written in the
    session workspace.
31. Inspected it with `wc -l baseline.wat` (395 lines) and
    `rg -n -C 8 "i64.const 99|struct.new|struct.set|local.set|drop|99" baseline.wat`.
    Relevant match at emitted line 381: `(drop (struct.new $ival (i64.const 99)))`.
32. Printed lines 373–395 and attempted a no-cell regex. The first regex was double-quoted, so shell
    expansion made it insufficiently literal; treated this inspection as inconclusive, not evidence.
33. Repeated correctly with single quotes:
    `rg -n 'struct\\.new \\$env.*i64\\.const 99' baseline.wat`; exit 1/no matches.
34. Used `apply_patch` to record the artifact excerpt and exact negative search in `evidence-t05.txt`.
35. T06 action 1: `bang query contract main.invalid.bang` -> exit 0 and top-level `ok:true`, while
    `evidence.typeChecked:false`, with a quantity mismatch error and `[1]`/`[omega]` facts.
36. Used `apply_patch` to preserve the entire T06 response and decision in `evidence-t06.txt`.
37. Read permitted language-reference lines 1030–1085 and 1328–1378. The public contract confirms
    `query` exit 0 means the operation ran and says `contract.evidence` records whether the merged
    program type-checks. This supports, but does not replace, the actual-response judgment in T06.
38. Listed workspace artifacts with `find ... -printf ... | sort`; confirmed the four program
    variants, Permit module, five evidence files, and `baseline.wat`, then created this report with
    `apply_patch`.

## Severity-ranked findings

### 1. High — query success is easy to confuse with subject validity

- **Observation:** For the invalid twice-used program, `query contract` exits 0 and returns
  top-level `ok:true`, yet `evidence.typeChecked:false` and an error. `check --json` for the same
  source exits 1 and returns `ok:false`.
- **Interpretation:** A naive consumer using the conventional `ok` field or process status as a
  validity gate can accept an invalid program. Consumers must know this command-specific schema and
  key on `evidence.typeChecked`.
- **Alternative explanations:** The public help/reference explicitly define top-level `ok` and exit
  0 as operation success, so this is documented behavior, not an implementation/contract mismatch.
  Keeping a partial semantic card for invalid input is useful; the usability risk is the overloaded
  success vocabulary.

### 2. Medium — the structured multi-file diagnosis has no source location

- **Observation:** Both B018 `check --json` responses have `span:null`.
- **Interpretation:** Automation can identify and explain the stable code, but cannot navigate
  directly to the offending `use [1] permit` in a resolved multi-file program.
- **Alternative explanations:** `bang --help` explicitly calls this a known v1 limitation, and the
  human-readable message quotes the offending assertion, so recovery remains practical in a small
  example.

### 3. Low — realization identifiers are not stable across an installation-only swap

- **Observation:** Baseline card realization names are `Identity` and `Permit_Negate`; swapped card
  names are `Permit_Identity` and `Negate`. Law `trait`/`realization` fields change in the same way,
  even though the module and its two declarations are unchanged.
- **Interpretation:** A machine diff may report more identity churn than the semantic change (which
  realization is installed), complicating before/after correlation.
- **Alternative explanations:** The names consistently reflect resolver qualification rules and the
  contract/operation content remains sufficient to correlate the records in this two-item example.

### 4. Informational — public recovery and compilation evidence are strong

- **Observation:** B018 points to `bang explain`; the explanation gives the correct widening rule;
  `query contract` exposes declared versus observed quantities; and emitted WAT makes preserved
  evaluation plus dead-cell omission directly inspectable.
- **Interpretation:** Once the consumer uses `evidence.typeChecked`, the public surfaces support the
  complete diagnose/recover/compare/compile journey without implementation access.
- **Alternative explanations:** The initial nested-call form required one extra reference search;
  that error was independent of resource quantities and not evidence that B018's advice was wrong.
