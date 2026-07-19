// Role-lab CONTENT only. Page identity, route, prerequisites, audience, order,
// first-edit seams, and gates live in page-manifest.json. Prose, checks, the
// disposable fixture, and additional seams are shared by each lesson and test.
export const kernelProofReference = Object.freeze({
  statement: 'Bang.subst_value',
  implementation: 'Bang.subst_value_proof',
  implementationDisplay: 'subst_value_proof',
  statementSource: 'Bang/Spec.lean',
  implementationSource: 'Bang/Core/Soundness.lean',
  auditSource: 'Bang/Audit.lean',
})

export const machineBackendReference = Object.freeze({
  constructor: 'Comp.binop',
  operation: 'BinOp.add',
  sourceDefinition: 'Bang/Core/IR.lean',
  sourceSemantics: 'Bang/Core/Semantics/Eval.lean',
  machineSource: 'Bang/Backend/AbstractMachine.lean',
  emitterSource: 'Bang/Backend/WasmEmit.lean',
  emitterHarness: 'tools/emit-rung1-diff.sh',
  expectedOutput: '42\n',
})

const machineBackendExpectedShell = machineBackendReference.expectedOutput.replaceAll('\n', '\\n')

export const roleLabContent = [
  {
    key: 'frontend-language',
    stages: [
      {
        id: 'retrieve-predict',
        prose: `
Retrieve the language and CLI contracts before editing. Read the formatter,
query, rewrite, and impact surfaces as one workflow: the formatter changes
presentation; the read model must keep reporting the same declarations,
reference edges, effects, impact closure, and result.
`,
        retrievalChecks: [
          'Locate the syntax and type-check seams named by this route.',
          'Locate the language/CLI reference for fmt, check --json, query, impact, and rewrite fmt.',
        ],
        predictionChecks: [
          'Predict the three declarations and their inferred types before running a query.',
          'Predict the direct double → quad edge and transitive double → quad → main impact.',
          'Predict the program result before formatting the source.',
        ],
      },
      {
        id: 'trace-seam',
        prose: `
Trace a frontend change from surface parsing through elaboration and its
focused executable gates. Start at the manifest-owned seams, then inspect the
CLI entry and query/rewrite tests that expose the user-visible boundary.
`,
        checks: [
          'Explain which seam owns parsing and which owns elaboration/type checking.',
          'Name the focused gate that can falsify the intended frontend change before the full gate.',
        ],
        seams: [
          'Bang/Frontend/Format.lean',
          'Bang/Frontend/Query.lean',
          'Bang/Frontend/Rewrite.lean',
          'Main.lean',
          'tools/test-fmt.sh',
          'tools/test-check-json.sh',
          'tools/test-query.sh',
          'tools/test-rewrite.sh',
          'tools/test-82-verbs.sh',
        ],
      },
      {
        id: 'isolated-practice',
        prose: `
Create this intentionally noncanonical program in a disposable full-clone
lane. Observe its facts first, prove rewrite diff mode does not mutate it, then
apply formatting with \`-w\`. Do not rename a declaration: this lab isolates
the formatting boundary.
`,
        fixture: {
          path: 'main.bang',
          source: `let rec double : Int -> Int = fun n => n+n
let quad = {fun n => $double ($double n)}
let main = $quad 3
`,
        },
        commands: [
          'nix develop --command lake build Bang.Frontend.TypeCheck',
          '"$bang" fmt "$practice"',
          '"$bang" check --json "$practice"',
          '"$bang" query dump "$practice"',
          '"$bang" query symbols "$practice"',
          '"$bang" query type "$practice" double',
          '"$bang" query effects double "$practice"',
          '"$bang" query def double "$practice"',
          '"$bang" query refs double "$practice"',
          '"$bang" impact "$practice" double',
          '"$bang" run "$practice"',
          '"$bang" rewrite fmt "$practice"',
          '"$bang" rewrite fmt "$practice" -w',
          'test "$(cat "$practice")" = "$("$bang" fmt "$practice")"',
          '"$bang" check --json "$practice"',
          '"$bang" query dump "$practice"',
          '"$bang" impact "$practice" double',
          '"$bang" run "$practice"',
        ],
        boundedOutcome: 'Only formatting changes: declarations, types, effects, reference edges, impact, and result remain equal.',
      },
      {
        id: 'inspect-select',
        prose: `
Treat the before/after observations as evidence, not a transcript to copy.
After the narrow and full gates pass, select current work by querying the live
issue tracker read-only and matching labels or descriptions to the traced
frontend seams.
`,
        evidenceChecks: [
          'Record the formatter output computed from the current binary; do not compare with a stored golden.',
          'Compare parsed before/after query facts and the observed result.',
          'Confirm rewrite diff mode left the disposable file byte-identical and write mode reached formatter content; fmt stdout adds one terminal newline that rewrite -w does not store.',
          'Run the route narrow gate, then the full gate, without treating a skipped step as a pass.',
          'Confirm the practice stayed in the disposable lane and made no push or GitHub mutation.',
        ],
        issueSelection: 'Run `gh issue list --repo phibkro/bang --state open --search "frontend OR parser OR type checker"`; set `issue=<candidate-number>` and inspect it with `gh issue view "$issue" --repo phibkro/bang`. This only supports a recommendation: do not claim, comment on, or mutate the issue.',
      },
    ],
  },
  {
    key: 'kernel-proof',
    stages: [
      {
        id: 'retrieve-predict',
        prose: `
Start from the frozen public claim, not from a tactic guess. Read
\`${kernelProofReference.statement}\` in \`${kernelProofReference.statementSource}\`,
state its claim in plain language, then locate
\`${kernelProofReference.implementationDisplay}\` in
\`${kernelProofReference.implementationSource}\`. Predict the kernel trust result
before consulting Audit. Changing the statement or adding a hypothesis is outside
this bounded exercise; use the proof-discipline note when you need the rule rather
than copying it here.
`,
        retrievalChecks: [
          `Locate the frozen \`${kernelProofReference.statement}\` statement in \`${kernelProofReference.statementSource}\`.`,
          `Locate \`${kernelProofReference.implementationDisplay}\` in \`${kernelProofReference.implementationSource}\` and the \`${kernelProofReference.statement}\` enrollment in \`${kernelProofReference.auditSource}\`.`,
          'Open `docs/notes/spec-proof-discipline.md` for the repository proof rules.',
        ],
        predictionChecks: [
          'Explain in plain language what substitution preserves and how the grade changes.',
          'Predict whether the current Audit result is trusted-three-only or flagged before running the census.',
          'Predict why changing the frozen statement or adding a hypothesis would evade rather than solve the exercise.',
        ],
      },
      {
        id: 'trace-seam',
        prose: `
Ownership is explicit: Spec owns the public statement; Soundness owns its proof;
\`tools/check.sh\` owns the fast local elaboration gate; Audit owns the enrolled
repository census. A local \`#print axioms\` answers only for the named scratch
theorem, while \`just axioms\` runs the enrolled Audit census. Its trusted three
are \`propext\`, \`Classical.choice\`, and \`Quot.sound\`: they are the maximum
permitted dependencies of enrolled theorems, not axioms contributors may add.
Source search and the marker-removal grep navigate or check workflow state; neither
is proof evidence.
`,
        checks: [
          'Name the statement owner, implementation owner, fast elaboration gate, and kernel trust evidence owner.',
          'Explain why a successful file check and an acceptable axiom report establish different facts.',
          'Use the tactics survey to interpret Lean suggestions without treating a suggested tactic as trusted evidence.',
        ],
        seams: [
          'Bang/Audit.lean',
          'docs/notes/spec-proof-discipline.md',
          'docs/notes/tactics-survey.md',
          'tools/check.sh',
        ],
      },
      {
        id: 'isolated-practice',
        prose: `
Create the root-level disposable fixture below; no production file imports it.
Predict the nil and cons induction cases, then run direct Lean once and inspect
the unique \`Try this:\` line produced by \`exact?\`. Manually replace only that
marker with Lean's current one-line suggestion. Do not copy a stored answer and
do not use \`simp?\`: the verified rewrite setup is what leaves a deterministic
closing suggestion. The displayed grep then checks only that this workflow edit
happened; it says nothing about axioms. Only after it passes run the clean check,
the scratch theorem's local report, and the enrolled repository census.
`,
        fixture: {
          path: 'KernelProofLab.lean',
          source: `import Bang.Core.Soundness

namespace Bang
namespace GradeVec

variable {M : Type}

theorem zero_smul_scratch [MulZeroClass M] (γ : GradeVec M) :
    GradeVec.smul 0 γ = GradeVec.zeros γ.length := by
  induction γ with
  | nil => rfl
  | cons a γ ih =>
    rw [smul_cons, zero_mul, List.length_cons, GradeVec.zeros,
      List.replicate_succ, ← GradeVec.zeros]
    exact?

#print axioms Bang.GradeVec.zero_smul_scratch

end GradeVec
end Bang
`,
        },
        commands: [
          'nix develop --command lake build Bang.Core.Soundness',
          'nix develop --command lake env lean "$practice" 2>&1 | tee "$bundle/scratch-suggestion.txt"',
          "if grep -Fq 'exact?' \"$practice\"; then printf '%s\\n' 'STOP: replace exact? with Lean current suggestion before continuing.' >&2; false; fi",
          'nix develop --command just check "$practice" 2>&1 | tee "$bundle/scratch-check.txt"',
          'nix develop --command lake env lean "$practice" 2>&1 | tee "$bundle/scratch-axioms.txt"',
          'nix develop --command just test-role-lab-kernel-proof 2>&1 | tee "$bundle/harness.txt"',
          'nix develop --command just axioms 2>&1 | tee "$bundle/audit-axioms.txt"',
          'cp "$practice" "$bundle/KernelProofLab.lean"',
          'rm "$practice"',
          'test -z "$(git status --porcelain)"',
        ],
        boundedOutcome: 'The disposable theorem closes without `sorry`, its own kernel report is empty, `Bang.subst_value` remains within the trusted-three baseline, and no production Lean source or import changes.',
      },
      {
        id: 'inspect-select',
        prose: `
Keep the completed scratch source and kernel reports as the evidence bundle.
Known-bad proofs that compile through \`sorry\` or a scratch-only declared axiom
must fail because parsed \`#print axioms\` output exposes their dependencies, not
because their source text was searched. Select live work read-only only after
you can name the statement owner, proof owner, and smallest falsifying gate.
`,
        evidenceChecks: [
          'Confirm the frozen statement and all production sources are unchanged.',
          'Confirm the completed scratch source has no suggestion placeholder and differs only at that marker.',
          'Require exactly one scratch theorem report with an empty axiom set.',
          'Require compiling `sorryAx` and unexpected scratch-axiom variants to be rejected from parsed kernel output.',
          'Require the current `Bang.subst_value` report to be a subset of the trusted three and contain no `sorryAx`.',
          'Record the real narrow and full gate exit statuses; a skipped gate is not a pass.',
        ],
        issueSelection: 'Run `gh issue list --repo phibkro/bang --state open --search "proof OR soundness OR kernel"`; set `issue=<candidate-number>` and inspect it with `gh issue view "$issue" --repo phibkro/bang`. Recommend one only after naming its statement owner, proof owner, and smallest falsifying gate; do not claim, comment on, or mutate it.',
      },
    ],
  },
  {
    key: 'machine-backend',
    stages: [
      {
        id: 'retrieve-predict',
        prose: `
Start from the existing \u0060${machineBackendReference.constructor}\u0060 constructor and
its source meaning. Locate the constructor in
\u0060${machineBackendReference.sourceDefinition}\u0060, then the closed-integer reduction
in \u0060${machineBackendReference.sourceSemantics}\u0060. Predict the disposable program's
observable value before running any engine. The task is to follow an existing
calculation, not to propose an instruction or optimize it.
`,
        retrievalChecks: [
          `Locate \u0060${machineBackendReference.constructor}\u0060 and \u0060${machineBackendReference.operation}\u0060 in \u0060${machineBackendReference.sourceDefinition}\u0060.`,
          `Locate the closed-integer \u0060${machineBackendReference.constructor}\u0060 arm in \u0060${machineBackendReference.sourceSemantics}\u0060.`,
          `Locate \u0060evalD\u0060, \u0060compile\u0060, \u0060exec\u0060, and \u0060Agree\u0060 in \u0060${machineBackendReference.machineSource}\u0060.`,
        ],
        predictionChecks: [
          'Predict the value of `19 + 23` before running env, oracle, or compiled.',
          'Predict whether compile/exec keeps an arithmetic instruction or collapses the closed operation to a return.',
          'Predict whether the Wasm emitter supports integer addition or must refuse it loudly.',
        ],
      },
      {
        id: 'trace-seam',
        prose: `
Trace one constructor through linked owners. The kernel step defines source
meaning; \u0060evalD\u0060 is the state-explicit denotation from which \u0060compile\u0060 and
\u0060exec\u0060 are calculated; \u0060Agree\u0060 ties \u0060exec ∘ compile\u0060 and \u0060Source.eval\u0060 to one
observable value. The Wasm emitter is a separate tested path from the same
\u0060Comp\u0060: its \u0060emitComp\u0060 arm emits supported arithmetic and its differential
harness compares Wasmtime with the kernel oracle. The calculated machine remains
an output of the calculation; this lab adds no instruction or semantic rule.
`,
        checks: [
          'Name the source step, evalD arm, compile arm, exec return behavior, and Agree observation without copying their bodies.',
          'Explain why compile/exec constant-folding and direct Wasm arithmetic emission may differ internally while sharing the source result.',
          'Explain how an explicit emitter refusal differs from an agreement failure or a silent skip.',
        ],
        seams: [
          machineBackendReference.sourceDefinition,
          machineBackendReference.sourceSemantics,
          machineBackendReference.emitterHarness,
        ],
      },
      {
        id: 'isolated-practice',
        prose: `
Create the fixture below only in the disposable exact-HEAD clone. Materialize its
expected output beside it, then run the same source through env, oracle, and
compiled; each engine must match that one expected file. Run the existing
\u0060Agree\u0060 battery and, because integer addition is supported, the existing rung-1
emitter differential. Do not edit a production Lean file or add a new machine
case. A refusal from a supported addition or any skipped engine is a failure.
`,
        fixture: {
          path: 'main.bang',
          source: `let main = 19 + 23
`,
        },
        commands: [
          'nix develop --command lake build bang',
          'expected="$lane/expected.txt"',
          `printf '${machineBackendExpectedShell}' > "$expected"`,
          './.lake/build/bin/bang run --engine=env "$practice" > "$bundle/env.txt" && diff -u "$expected" "$bundle/env.txt"',
          './.lake/build/bin/bang run --engine=oracle "$practice" > "$bundle/oracle.txt" && diff -u "$expected" "$bundle/oracle.txt"',
          './.lake/build/bin/bang run --engine=compiled "$practice" > "$bundle/compiled.txt" && diff -u "$expected" "$bundle/compiled.txt"',
          'nix develop --command just check Bang/Backend/AbstractMachine.lean > "$bundle/agree.txt" 2>&1',
          'nix develop --command bash tools/emit-rung1-diff.sh > "$bundle/emitter.txt" 2>&1',
          'nix develop --command just test-role-lab-machine-backend > "$bundle/harness.txt" 2>&1',
          'cp "$practice" "$expected" "$bundle"',
          'rm "$practice" "$expected"',
          'test -z "$(git status --porcelain)"',
        ],
        boundedOutcome: 'The disposable source yields 42 under env, oracle, and compiled; the Agree battery elaborates; the supported addition sample emits and agrees with Wasmtime; cleanup leaves the exact-HEAD lane unchanged.',
      },
      {
        id: 'inspect-select',
        prose: `
Keep the three engine outputs, \u0060Agree\u0060 check, emitter report, source, and expected
file as one evidence bundle outside the disposable clone. Agreement means all
observations equal the committed expected value. Unsupported means the emitter
returns and reports an explicit refusal; it never means a missing result or an
unrun command. Select live backend work read-only only after naming the owning
module and the smallest gate that can falsify a change on this seam.
`,
        evidenceChecks: [
          'Require env, oracle, and compiled to run exactly once and match the same expected file.',
          'Confirm a deliberately wrong expected value would reject every captured engine output.',
          'Require the AbstractMachine check to exercise the existing Agree battery.',
          'Require the emitter report to include the supported integer-add sample, no refusal, and a Wasmtime/oracle agreement verdict.',
          'Confirm no production Lean source changed and cleanup returned the exact-HEAD lane to a clean state.',
          'Record the real narrow and full gate exit statuses; a skipped gate is not a pass.',
        ],
        issueSelection: 'Run `gh issue list --repo phibkro/bang --state open --search "backend OR CalcVM OR Wasm OR emitter"`; set `issue=<candidate-number>` and inspect it with `gh issue view "$issue" --repo phibkro/bang`. Recommend one only after naming its owning module, semantic oracle, and smallest falsifying gate; do not claim, comment on, or mutate it.',
      },
    ],
  },
]
