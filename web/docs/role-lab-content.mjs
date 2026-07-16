// Role-lab CONTENT only. Page identity, route, prerequisites, audience, order,
// and gates live in page-manifest.json. The disposable fixture is shared by
// the generated lesson and its executable test.
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
        issueSelection: 'Run `gh issue list --repo phibkro/bang --state open --search "frontend OR parser OR type checker"`; inspect candidates with `gh issue view --repo phibkro/bang`, then choose one whose requested change crosses a traced seam.',
      },
    ],
  },
]
