# BANG resource-contract usability session — example-first participant

Session workspace: `/tmp/bang-session-example-first`

Revision under test: frozen product tree `/tmp/lang-bang-rebase.HtbDJs` (`d48b7d33` plus
parent feature commit `4fef991e`, as supplied by the task packet). I did not inspect git history
or implementation, and did not edit the product tree.

Counting convention: an action is one participant-facing read/list, source-edit batch, or BANG CLI
invocation used to advance a task. Pure evidence copying/report writing is not counted. No task
reached the 20-action limit.

## Administrative pre-trace

1. Read `/tmp/bang-resource-contract-task-packet.md` completely. Assumption: the explicit allowlist
   overrides links in public documents, so linked but non-allowlisted documents must not be opened.
2. Ran a setup command that asserted the session path did not exist, created
   `/tmp/bang-session-example-first`, and tried to list permitted top-level material. The `find`
   expression overmatched and printed filenames such as `paths/README.md`, `plans/README.md`, and
   other out-of-scope README paths. No contents, metadata beyond paths, or follow-up reads occurred.
   This is one administrative detour, recorded immediately; all later reads were explicitly rooted
   in the allowlist.

## T01 — Orient

Outcome: success. BANG is trying to separate semantic descriptions of computations, effects, and
resource obligations from their realizations, while retaining compiler/evaluation evidence. The
smallest explicitly indexed example combining a semantic contract and a local resource obligation is
`examples/resource-contract`: `Permit.bang` declares `Permit.spend`, its `preserves_zero` law, and
`Identity`/`Negate` realizations; `main.bang` adds `use [1] permit` and `use [0] ghost`.

First-attempt status: passed on the first orientation path.

Counts: 3 actions, 0 errors, 0 task-local detours.

Oracle evidence: `README.md` describes semantic descriptions and deferred observation;
`examples/README.md` labels `resource-contract` the semantic-contract tracer; the fixture's own
README and source show the law, alternatives, and `[0]`/`[1]` obligations. `expected.txt` says `7`.

Trace:

1. Consulted `README.md` and `ONBOARDING.md` with `sed`. Relevant result: README calls BANG “a small
   language of semantic descriptions” and says descriptions survive toward WebAssembly; onboarding
   identifies `check --json` versus `query dump` and the three engines. Assumption formed: examples
   and their expected files are executable user oracles, but prose claims still need CLI confirmation.
2. Ran `rg --files examples | sort`. Relevant result: found `examples/resource-contract/{Permit.bang,
   README.md,expected.txt,main.bang}` among the allowed example corpus. No error.
3. Consulted `examples/README.md`, `examples/resource-contract/README.md`, `Permit.bang`, `main.bang`,
   and `expected.txt`. Relevant result: the corpus index explicitly identifies this fixture; source
   confirms one operation, one law, two realizations, an unused `ghost`, and exactly-once `permit`;
   expected output is `7`.

## T02 — Establish the example's evidence

Outcome: success. Observable result is `7`; both alternative realizations meet the shared
`preserves_zero` law; `query contract` returns a single machine-readable document joining contract,
realizations, quantities, laws, and compiler evidence.

First-attempt status: all three evidence commands succeeded on their first invocation.

Counts: 4 actions, 0 errors, 0 detours.

Oracle evidence:

- `t02-run.txt`: `7`.
- `t02-laws.txt`: `Permit@Identity.preserves_zero` PASS and `Permit@Negate.preserves_zero` PASS,
  each over 30 samples; `laws: 2/2 passed`.
- `t02-contract.json`: top-level `ok:true`; one contract; both realizations; `ghost` `[0]` observed
  `[0]`; `permit` `[1]` observed `[1]`; both law bodies; `evidence.typeChecked:true`, exact-local
  checking, pre-lowering quantity erasure, and `manifest-unused-let-result` backend evidence.

Trace:

1. Ran `./.lake/build/bin/bang --help`. Relevant result: learned the public contracts for `run`,
   decls-only `test`, `query contract`, `emit`, and exit status. Assumption: use the already-built
   binary directly rather than rebuilding via `lake exe`.
2. Ran `bang run examples/resource-contract/main.bang`; exit 0, stdout `7`.
3. Ran `bang test examples/resource-contract/Permit.bang`; exit 0, both named realizations PASS,
   summary `2/2 passed`.
4. Ran `bang query contract examples/resource-contract/main.bang`; exit 0 and the joined JSON
   summarized above. Preserved the relevant outputs under the session workspace.

## T03 — Make and recover from a realistic mistake

Outcome: success. I duplicated `permit.spend` while leaving the obligation `[1]`. The checker refused
the program because two sequential uses are observed as `[omega]`. The public language reference says
`[omega]` is unrestricted and sequential uses saturate there, so I changed the obligation to
`use [omega] permit` without deleting either call. The recovered program checks and evaluates to `9`.

First-attempt status: the intended invalidity was diagnosed on the first check, and the first recovery
edit was accepted.

Counts: 7 actions, 1 expected product error, 0 detours.

Oracle evidence: `t03-invalid-diagnostic.txt` records exit 1 and
`quantity mismatch: 'use [1] permit' requires [1], but the body has [omega]`;
`main-recovered.bang` retains both calls; recovered `bang check` returned `ok` and `bang run` returned
`9`.

Trace:

1. Created `main-invalid.bang` beside a copy of the public `Permit.bang`, changing the body to
   `permit.spend(7) + permit.spend(2)` while retaining `[1]`. Assumption: sequential occurrences count
   as two uses, but I did not yet assume the recovery syntax.
2. Ran `bang check main-invalid.bang`; exit 1 with the exact mismatch above. This is the one intended
   product error. Interpretation at this point: `[1]` is genuinely checked, not documentary.
3. Searched only the permitted public `docs/reference/language.md` for `quantity`, `omega`, `use [`,
   and `resource`. Relevant hits were the syntax table and the local-resource-obligation explanation.
4. Read the hit ranges in `docs/reference/language.md`. Relevant public help: `[0]` means zero,
   `[1]` exactly once on each branch, `[omega]` unrestricted; sequential uses add and saturate at
   omega; assertions erase before lowering.
5. Created `main-recovered.bang`, changing `[1]` to `[omega]` and keeping both spends.
6. Ran `bang check main-recovered.bang`; exit 0, stdout `ok`. Recovery confirmed.
7. Ran `bang run main-recovered.bang`; exit 0, stdout `9` (Identity returns 7 and 2).

What the diagnosis taught me: the checker reports both the declared and inferred quantity. Multiple
sequential uses are collapsed to the unrestricted grade `[omega]`; the fix is to make the local
promise honest, not to disable type checking or remove the behavior.

## T04 — Transfer the semantic model

Outcome: success. Swapping the installed realization to `Negate` changed the observable result while
leaving the shared computation and law intact.

First-attempt status: prediction and all post-swap checks were correct/successful on the first attempt.

Counts: 5 actions, 0 errors, 0 detours.

Oracle evidence: `t04-prediction.txt` predates execution and predicts `-7` plus continued law success;
`t04-check.txt` is `ok`; `t04-run.txt` is `-7`; `t04-laws.txt` remains `2/2 passed`;
`t04-contract.json` keeps the same contract, both realization law bodies, both matching quantities,
and `typeChecked:true`.

Trace:

1. Created `main-negate.bang`, changing only imported/installed handler names from Identity to Negate;
   the computation remains `permit.spend(7)`. Recorded before running: expected result `-7`, and
   expected `preserves_zero` to hold because `0 - 0 == 0`.
2. Ran `bang check main-negate.bang`; exit 0, `ok`.
3. Ran `bang run main-negate.bang`; exit 0, `-7`, matching the prediction and differing from T02's `7`.
4. Ran `bang test Permit.bang`; exit 0, both original law instances still PASS, `2/2`.
5. Ran `bang query contract main-negate.bang`; exit 0, `ok:true`, `typeChecked:true`, the same matching
   `[0]` and `[1]` quantities. Comparison note: the explicitly imported realization now has the short
   name `Negate`; the other is serialized as `Permit_Identity`, reversing the alias pattern from the
   Identity-installed card (`Identity` / `Permit_Negate`).

## T05 — Inspect a concrete compilation consequence

Outcome: success. The unused binding expression still runs, but no runtime environment cell is
retained for its value.

First-attempt status: emit succeeded first try; artifact inspection found the evidence in one broad
search followed by a focused excerpt.

Counts: 3 actions, 0 errors, 1 detour (the first WAT search was broader/noisier than necessary).

Oracle evidence: `t05-resource-contract.wat`, lines 377–393. In `_start`, line 381 is
`(drop (struct.new $ival (i64.const 99)))`: constructing/boxing `99` demonstrates evaluation and
immediate `drop` demonstrates the unused result is discarded. The following `$env` cells retain a
handler parameter/closure/capability; the literal `99` has no other occurrence, so there is no
environment-cell retention for `ghost`.

Trace:

1. Ran `bang emit main-original.bang -o t05-resource-contract.wat`; exit 0, artifact created.
2. Searched generated WAT for `99|array|struct|local.set|drop`. It found the needed `_start` line but
   also much unrelated runtime support because `struct` and `local.set` were broad terms. Recorded as
   a navigation detour, not a product failure.
3. Printed numbered lines 373–396. Relevant result: line 381 constructs and drops 99 before the body;
   lines 383–391 construct only the handler/capability environment needed for `spend(7)`.

## T06 — Judge machine-readable invalidity

Outcome: success. A naive consumer can mistake operation success for program validity: the query exits
0 and returns top-level `"ok":true` even for the twice-used invalid source. The safest validity signal
inside this response is `evidence.typeChecked`, which is `false`; consumers should also surface
`evidence.error`. Top-level `ok` means the query operation produced an answer, not that the program
passed resource checking.

First-attempt status: the invalid query completed and exposed the distinction on the first attempt.

Counts: 1 action, 0 errors (the query operation succeeded), 0 detours.

Oracle evidence: `t06-exit.txt` is `0`; `t06-invalid-contract.json` contains top-level `ok:true`, the
permit quantity `declared:"[1]"` versus `observed:"[omega]"`, and
`evidence:{"typeChecked":false,"error":"quantity mismatch: ..."}`.

Trace:

1. Ran `bang query contract main-invalid.bang` while capturing process status. Exit was 0. The JSON
   still supplies the contract/realization/law card and the mismatching quantity, with top-level
   `ok:true`; nested compiler evidence says `typeChecked:false` and contains the exact mismatch.
   Decision from actual response: do not use exit 0 or top-level `ok` as a program-validity oracle;
   require `evidence.typeChecked === true`.

## Severity-ranked findings

### High — query-operation success can be confused with program validity

Observation: `query contract` on the invalid duplicate-use file exits 0 and says top-level `ok:true`,
while only `evidence.typeChecked:false` marks invalidity. The card otherwise looks rich and complete.

Interpretation: naive automation that follows a conventional `exit == 0 && ok == true` rule can admit
an invalid program. The safest current integration rule is to require `evidence.typeChecked === true`.

Alternative explanation: CLI help explicitly defines query exit 0/top-level success as “the op ran and
produced an answer,” so the behavior may be intentional. The usability risk remains because two
different meanings of success coexist in one response without a top-level validity field.

### Medium — quantity diagnostics lack the advertised stable-code/explain recovery route

Observation: the useful quantity mismatch was emitted as `error: quantity mismatch...` with no stable
`Bxxx` code or `explainCode`. Public `--help` advertises `bang explain <CODE>` for coded diagnostics,
so it could not be used here; recovery required searching the long language reference.

Interpretation: a newcomer can recover, and the diagnostic helpfully exposes `[omega]`, but the path is
less discoverable than coded errors and structured diagnostics.

Alternative explanation: resource obligations may be too new to have a stable diagnostic code, and the
human message plus permitted reference were sufficient in this session.

### Low — realization names in joined cards depend on the selected import alias

Observation: the Identity-installed card names realizations `Identity` and `Permit_Negate`; the
Negate-installed card names them `Permit_Identity` and `Negate`, although the underlying declarations
and laws are unchanged.

Interpretation: machine consumers comparing cards across handler swaps may see identifier churn beyond
the semantic change and need to normalize names.

Alternative explanation: this can be an intentional faithful presentation of module-name resolution:
the selected imported name is locally short and the non-imported sibling remains qualified.

### Low — emitted evidence is strong but source-to-artifact navigation is manual

Observation: the emitted WAT makes the `[0]` consequence concrete (`construct 99; drop; no env cell`),
but finding it required text search and manual reasoning because the artifact carries no source label
for `ghost`.

Interpretation: the evidence is auditable for this tiny example but may be harder to trace in a larger
program.

Alternative explanation: WAT is a low-level compiler artifact, and the joined query already supplies
the higher-level `manifest-unused-let-result` summary; explicit source mapping may be outside this
command's scope.
