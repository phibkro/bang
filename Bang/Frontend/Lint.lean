/-
  Bang/Frontend/Lint.lean — the `bang lint` rule package (#82 item 2): rules as QUERIES over the
  dump fact base, no new analysis machinery.
  ─────────────────────────────────────────────────────────────────────────────────────────────
  RULES ARE QUERIES (the operator's own #82 framing): every rule below is a pure re-derivation of
  `Bang.Query`'s Tier-1 facts (`declFactsOf`/`nameRefEdgesOf`/`surfUsesVar`) — this module adds NO
  new checking/reachability primitive. It mirrors `tools/DeadCode.lean`'s own Lean-side discipline
  (root set → transitive-closure BFS over reference edges → unreachable-set report, ADVISORY not a
  gate, "genuine orphan vs intentional park" reading distinction) at the SURFACE-program level: a
  `bang.bang` program's own `pubNames`/trailing `body` are the roots (the CLI analogue of
  `DeadCode.lean`'s Audit-headline + `main` root set), `nameRefEdgesOf` + the body's own free-var
  scan are the reference edges, and `declared-but-unreachable` is the finding.

  THREE RULES (v1, #82's own ranked list minus "shadowed bindings" — deferred, no fact seam exists
  yet for a shadowing SITE at decl-granularity; a forward pointer, not a scope cut silently made):

    `dead-private`  — a NON-`pub` top-level decl unreachable from the roots (`pubNames` ∪ `body`'s
      own free vars), closure-computed over `nameRefEdgesOf` exactly like `DeadCode.lean`'s BFS.
      SEVERITY warning (a private decl nobody uses is very likely deletable — the ADVISORY caveat
      still applies: a decl reachable only through a currently-`typeError`'d sibling under-reports,
      mirroring `DeadCode.lean`'s own "sorry-gapped-live" honesty note, restated for this domain as
      "a decl whose own body fails to type-check may still reference names the closure never sees
      the EDGE for" — `Query.declMentionsVar`'s scan is SYNTACTIC, not type-gated, so this specific
      failure mode does not actually apply here; noted for parity with the Lean-side tool's caveat
      shape, not because the same mechanism recurs).
    `unused-pub`    — a `pub` top-level decl referenced by NOTHING in the module set (never from
      any OTHER decl, never from `body`) — SEVERITY info (a library's public surface legitimately
      has entries only an EXTERNAL importer uses; "unused within this file" is a much weaker signal
      than `dead-private`'s "unreachable from anything, including exports").
    `fmt-divergence` — the file's own source does not equal `Bang.Format.fmtProg` applied to
      itself — SEVERITY warning, WHOLE-FILE (not per-decl: `fmtProg` re-lays out the entire
      program, so a single finding names the file, with `bang rewrite fmt` as the fix pointer,
      rather than trying to attribute the diff to one decl).

  OUTPUT: a `LintReport` (`findings : List Finding`) — `Main.lean`'s `runLint` renders it as a
  human table (default) or `--json` (agent-consumable), with the `bang check --json` exit-code
  convention (#59's own precedent, extended here): exit 0 on `findings.isEmpty` OR when EVERY
  finding is below the reporting threshold and `--quiet-clean` was not needed to silence a genuine
  empty report; exit 1 on any finding at `warning` or above (severities are ORDERED so a future
  `--min-severity` is a threshold FILTER over this same list, not a new query). `--quiet-clean`
  (task #40's own naming) suppresses the "0 findings" success line for a scripted/CI caller that
  only wants nonzero-exit-on-real-findings, mirroring `check --json`'s "the caller inspects `ok`"
  convention applied to a human-table default instead of JSON.

  This is a LEAF module (`Bang/Frontend/*`, fan-in 0): reads `Bang.Query`'s public Tier-1 facts
  (`declFactsOf`/`nameRefEdgesOf`/`surfUsesVar`) and `Bang.Format.fmtProg`, produces only
  `Finding`/`LintReport` values (or a JSON string). No kernel/typing-rule change, no new checking
  behavior.
-/
module

meta import Bang.Frontend.Query
public import Bang.Frontend.Query
public import Bang.Frontend.Format

open Bang
open Bang.Surface (Decl Prog)

namespace Bang.Lint

/-! ## 1. Severity + Finding — the shared shape every rule emits. -/

/-- `info` < `warning` in the DECLARATION order below (no `Ord` instance derived — no rule below
compares severities; `Main.lean`'s exit-code arm matches on the constructor directly, and a future
`--min-severity` threshold would add its own comparison then, not speculatively here). -/
public inductive Severity where
  | info | warning
  deriving Repr, DecidableEq

public def Severity.toString : Severity → String
  | .info    => "info"
  | .warning => "warning"

/-- One lint finding: WHICH rule, at what severity, naming WHICH decl (`none` for a whole-file
finding like `fmt-divergence`), with a human-readable message. DECL granularity throughout
(matches `Query.RefEdge`'s own documented ceiling, #52 — no per-node span exists yet). -/
public structure Finding where
  rule     : String        -- the stable machine key: "dead-private" | "unused-pub" | "fmt-divergence"
  severity : Severity
  decl     : Option String  -- the flagged decl's name, or `none` for a whole-file finding
  message  : String
  deriving Repr

-- `deriving Repr`'s generated `repr` ignores its `prec` arg; `prec` is the interface, not
-- a dead param (unusedArguments false-positive on derived instances).
attribute [nolint unusedArguments] instReprFinding.repr

/-! ## 2. `dead-private` — the surface-level DeadCode.lean analogue.

Root set: every `pub` name (`p.pubNames`) PLUS every free variable `p.body` itself mentions (the
program's own trailing expression — the "what actually runs" root, mirroring `DeadCode.lean`'s
`main`/Audit-headline roots) PLUS, when `p` declares a top-level decl literally NAMED `main`, that
name itself — `Main.lean`'s own `runSource`/D5 convention (ADR-0093): a decls-only (`isLibrary`)
program with a `main` decl runs `main` AS the program (`body := Surf.var "main"` is substituted in
BEFORE execution), so `main` is a root by the SAME convention `bang run` itself uses, not merely
"whatever `p.body` happens to mention" — the p.body-only root set was WRONG for exactly this class
of program (every example in `examples/*/main.bang` is `main`-shaped) until this fix: it flagged
BOTH `main` and everything `main` alone references as `dead-private`, a false positive found while
building this rule's own CLI test. Closure: BFS over `nameRefEdgesOf`'s `src → tgt` edges, seeded
by the roots, same shape as `DeadCode.lean.reachable`. A NON-pub decl outside the closure is
`dead-private`. -/

/-- Every top-level decl name `p.body` mentions directly — the BODY's own root contribution
(`Query.surfUsesVar`, now `public`, applied to each candidate name; `O(decls)` per call, fine at
bang-program scale — mirrors `nameRefEdgesOf`'s own documented `O(decls²)` cost note). -/
def bodyRootNames (p : Prog) : List String :=
  (p.decls.map Bang.Surface.Decl.name).filter (Bang.Query.surfUsesVar · p.body)

/-- Does `p` declare a top-level decl named `main`? The D5/`runSource` convention's own root
condition (see this section's header) — `declFactsOf` reuse, ONE construct with `Rewrite.declares`. -/
def declaresMain (p : Prog) : Bool :=
  p.decls.any (·.name == "main")

/-- Transitive closure over `edges` (`Query.RefEdge`'s `src`/`tgt` list), seeded by `roots` — a
plain worklist BFS, the SAME algorithm shape `DeadCode.lean.reachable` uses over
`getUsedConstantsAsSet`, specialized to this module's flat edge-list fact instead of a Lean
`Environment`. `fuel` bounds the loop (this module is a LEAF — no `partial def`, the `bigFuel`
idiom: `edges.length + roots.length + 1` is always enough since each step either terminates the
worklist or adds a name never seen before, and there are at most `edges.length` distinct target
names to ever add). -/
def closure (edges : List Bang.Query.RefEdge) (roots : List String) (fuel : Nat) : List String :=
  go fuel roots roots
where
  go : Nat → List String → List String → List String
  | 0,     _,     seen => seen
  | _+1,   [],    seen => seen
  | f+1,   n::ws, seen =>
      let next := edges.filterMap (fun e => if e.src == n && !seen.contains e.tgt then some e.tgt else none)
      go f (next ++ ws) (next.foldl (fun acc m => if acc.contains m then acc else m :: acc) seen)

#guard ((closure [] ["a"] 5).toArray.qsort (·<·)).toList == ["a"]
#guard ((closure [(⟨"a", "b"⟩ : Bang.Query.RefEdge)] ["a"] 5).toArray.qsort (·<·)).toList == ["a", "b"]
#guard ((closure [(⟨"a", "b"⟩ : Bang.Query.RefEdge), ⟨"b", "c"⟩] ["a"] 5).toArray.qsort (·<·)).toList == ["a", "b", "c"]
-- an edge NOT reachable from the roots contributes nothing: `d` unreferenced by anything reachable from `a`.
#guard ((closure [(⟨"a", "b"⟩ : Bang.Query.RefEdge), ⟨"x", "d"⟩] ["a"] 5).toArray.qsort (·<·)).toList == ["a", "b"]

/-- **PUBLIC (rule 1):** every NON-`pub` top-level decl of `p` unreachable from the roots
(`pubNames` ∪ `bodyRootNames` ∪ `{"main"}` when declared) — `dead-private`, severity `warning`. -/
public def deadPrivateFindings (p : Prog) : List Finding :=
  let edges := Bang.Query.nameRefEdgesOf p
  let mainRoot := if declaresMain p then ["main"] else []
  let roots := p.pubNames ++ bodyRootNames p ++ mainRoot
  let fuel := edges.length + roots.length + 1
  let live := closure edges roots fuel
  p.decls.filterMap (fun d =>
    let n := d.name
    if !p.pubNames.contains n && !live.contains n then
      some ⟨"dead-private", .warning, some n,
            s!"'{n}' is a private top-level declaration unreachable from the program's public \
              surface or its own trailing body — likely dead code (delete it), or a genuine \
              parked case (nothing in this rule distinguishes the two, matching DeadCode.lean's \
              own advisory reading — see docs/reference/language.md's `bang lint` section)"⟩
    else none)

/-! ## 3. `unused-pub` — a `pub` decl no OTHER decl (or `body`) references. -/

/-- **PUBLIC (rule 2):** every `pub` top-level decl of `p` referenced by NOTHING within the module
(no OTHER decl's body, and not `p.body` itself) — `unused-pub`, severity `info` (a library's
public surface legitimately has externally-consumed entries this module set alone cannot see). -/
public def unusedPubFindings (p : Prog) : List Finding :=
  let edges := Bang.Query.nameRefEdgesOf p
  let bodyRoots := bodyRootNames p
  p.pubNames.filterMap (fun n =>
    let referencedByDecl := edges.any (·.tgt == n)
    if !referencedByDecl && !bodyRoots.contains n then
      some ⟨"unused-pub", .info, some n,
            s!"'{n}' is declared `pub` but nothing in this module references it — either an \
              external consumer uses it (expected for a library surface) or it is stale \
              (consider removing `pub` or the decl itself)"⟩
    else none)

/-! ## 4. `fmt-divergence` — the file's own source vs its canonical re-layout. -/

/-- Strip exactly ONE trailing `\n`, if present — the SAME convention `Main.lean`'s own
`stripTrailingNewline` documents (a well-formed text FILE ends in a newline the shell/editor
added, not a semantic part of the program, vs `Format.showProg`'s output, which never appends
one) — duplicated here rather than imported since `Main.lean` is the unrestricted Apex-rank
consumer of THIS leaf module, not the reverse (a leaf cannot import upward). -/
def stripTrailingNewline (s : String) : String :=
  if s.endsWith "\n" then s.dropRight 1 else s

/-- **PUBLIC (rule 3):** does `src` already equal its own canonical formatting? `none` when yes (no
finding), `some msg` when `fmtProg src` diverges OR fails to re-parse (a defensive case — `fmtProg`
round-trips through the SAME parser that already accepted `src`, so a failure here would itself be
a `Format.lean`-level bug, reported rather than silently swallowed, ADR-0046). WHOLE-FILE (module
header) — the fix pointer is `bang rewrite fmt -w`, not a per-decl edit. -/
public def fmtDivergenceFinding (src : String) : Option Finding :=
  match Bang.Format.fmtProg src with
  | .error e =>
      some ⟨"fmt-divergence", .warning, none,
            s!"the file failed to re-parse through its own canonical formatter ({e}) — this is \
              unexpected for a file that already parsed; report upstream"⟩
  | .ok canonical =>
      if stripTrailingNewline src == canonical then none
      else some ⟨"fmt-divergence", .warning, none,
                  "the file's layout differs from its canonical form — run `bang rewrite fmt -w` \
                  to fix (or `bang fmt` to preview)"⟩

/-! ## 5. The PUBLIC entry: every rule, over one `(src, Prog)` pair — `Main.lean`'s `runLint`
consumes this directly (parses `src` once, threads BOTH the raw string (`fmt-divergence`) and the
parsed `Prog` (the decl-fact rules) through one call). -/

/-- **PUBLIC entry:** run every rule over `src`/`p`, concatenated in RULE order (`dead-private` →
`unused-pub` → `fmt-divergence`) — a stable, documented order so `--json` output is deterministic
run-to-run for the SAME input (no rule reorders its own findings; `Main.lean` sorts by decl name
within a rule if a stronger order is ever needed, not added speculatively here). -/
public def lintProg (src : String) (p : Prog) : List Finding :=
  deadPrivateFindings p ++ unusedPubFindings p ++
    (match fmtDivergenceFinding src with | some f => [f] | none => [])

end Bang.Lint
