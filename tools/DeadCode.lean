/-
  tool: role=check couples=Bang/Audit.lean,Main.lean,deadcode-allow.txt runs-in=manual
  DeadCode.lean — the advisory dead-code fitness function.

  Run: `just dead-code`  (= `lake env lean tools/DeadCode.lean`).

  Reports every real `Bang.*` user declaration (theorem/def/opaque/axiom) NOT
  transitively reachable from the ROOT set — the verification spine (every
  `#print axioms` headline in `Bang/Audit.lean`) plus the `bang` CLI entry
  (`Main.main`). Roots pull their whole transitive closure via
  `ConstantInfo.getUsedConstantsAsSet`; anything outside that closure is either
  a genuine orphan (delete it) or an intentional park (list it in
  `tools/deadcode-allow.txt`).

  Auto-generated declarations (recursors, `.eq_N`, `match_`, `injEq`, `ctorIdx`,
  …) are excluded via Batteries' `isAutoDecl` — the canonical "is this a real
  user decl" predicate, so the noise floor is the library's, not a hand-rolled
  suffix list. On top of it we drop `deriving`-instance internals
  (`instReprFoo.repr`, `instDecidableEqBar.decEq`, …) and structure projections
  (`Environment.isProjectionFn`), which `isAutoDecl` does not cover.

  ADVISORY, never a gate. The route-1 rename chain (deleted at 58387c8) is
  exactly what this would have flagged the week it orphaned — that forensic win,
  made standing. The named upstream `#list_unused_decls`
  (Mathlib.Tactic.FindUnused) is absent from our pinned Mathlib v4.30.0; this is
  the same transitive-closure-from-roots analysis over available deps (core
  `getUsedConstantsAsSet` + importGraph `getModuleFor?` + Batteries `isAutoDecl`),
  the algorithm Batteries' `#show_unused` also uses — generalized here to the
  whole `Bang.*` environment rather than one file.

  This file is OUTSIDE the `Bang.+` lake glob (like `Main.lean`), so it is not in
  the `lake build` closure — it runs on demand, exactly as `Bang/Audit.lean` does.
  It imports EVERY `Bang.**` module (below, generated) + `Main` so the analyzed
  environment contains every declaration — including a module orphaned by nothing,
  the exact class a "reachable from Audit's closure" import list would miss. The
  trailing `#eval` reads that environment and prints the advisory report.

  The import block is GENERATED (drift-free) by `tools/gen-deadcode-imports.py`
  from `find Bang -name '*.lean'`; a new module is picked up on regen. Do not
  hand-edit between the GEN markers.
-/
-- BEGIN GEN deadcode-imports (tools/gen-deadcode-imports.py) --
import Main
import Bang.Audit
import Bang.Backend.AbstractMachine
import Bang.Backend.EnvMachine
import Bang.Backend.U5bComplete
import Bang.Backend.Wasm
import Bang.Core.CapCoh
import Bang.Core.EffectRow
import Bang.Core.Freshness
import Bang.Core.Grade
import Bang.Core.IR
import Bang.Core.Semantics
import Bang.Core.Semantics.Dispatch
import Bang.Core.Semantics.Eval
import Bang.Core.Semantics.Invariants
import Bang.Core.Semantics.Subst
import Bang.Core.Soundness
import Bang.Core.Typing
import Bang.Distribution
import Bang.Examples
import Bang.Frontend.Diagnostics
import Bang.Frontend.Format
import Bang.Frontend.NamedCore
import Bang.Frontend.Surface
import Bang.Frontend.Surface.PropTest
import Bang.Frontend.Surface.Trait
import Bang.Frontend.TypeCheck
import Bang.Meta.BinaryLR
import Bang.Meta.LR
import Bang.Reify.CalcReify
import Bang.Reify.CalcReifyRef
import Bang.Reify.CalcReifySim
import Bang.Spec
import Bang.Witness.AgreeOutcome
import Bang.Witness.BoccRegress
import Bang.Witness.CapEscapeWitness
import Bang.Witness.CustomStage1Refute
import Bang.Witness.ElabFuzz
import Bang.Witness.Fuzz
import Bang.Witness.LWRegress
import Bang.Witness.LawTest
import Bang.Witness.ProofExport
import Bang.Witness.ReturnEscapeReach
import Bang.Witness.StateEscapeWitness
import Bang.Witness.VcapFreeRefute
-- END GEN deadcode-imports --
import ImportGraph.Lean.Environment
import Batteries.Tactic.Lint.Basic

open Lean Elab Command Batteries.Tactic.Lint

namespace Bang.Tools.DeadCode

/-- The root set: the Audit-headline verification spine + the `bang` CLI entry.
    A declaration is LIVE iff transitively reachable from these. This list is a
    projection of `Bang/Audit.lean`'s `#print axioms` headlines (kept honest by
    the falsification test — a headline dropped here would make its whole subtree
    read as dead). -/
def roots : List Name :=
  [ ``lr_sound, ``lr_fundamental, ``lr_fundamental_closed, ``seq_unit,
    ``compile_forward_sim, ``Bang.compile_forward_sim_pure, ``Bang.source_eval_to_exec,
    ``compile_well_typed, ``handler_compiles, ``zero_grade_no_code, ``subst_value,
    ``preservation, ``progress, ``type_safety, ``no_accidental_handling,
    ``no_accidental_handling_custom, ``custom_program_safe, ``rowinst_requires_disjoint,
    ``effect_sound, ``zero_usage_erasable, ``Bang.Surface.cell_reflects_latest,
    ``Bang.CalcVM.compile_correct, ``Bang.CalcVM.evalD_agrees_source,
    ``Bang.CalcVM.sim, ``Bang.CalcVM.run_evalD,
    ``main ]

/-- Transitive-closure BFS over `getUsedConstantsAsSet`, seeded by `roots`. -/
partial def reachable (env : Environment) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work : Array Name := roots.toArray
  while h : work.size > 0 do
    let n := work.back
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for m in ci.getUsedConstantsAsSet do
        if !seen.contains m then work := work.push m
  return seen

/-- In a `Bang.*` module? -/
def inBangModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleFor? n with
  | some m => (`Bang).isPrefixOf m
  | none => false

/-- Does the name carry an instance-generated component (`instReprFoo`,
    `instDecidableEqBar`, …)? Their internals (`.repr`/`.decEq`/`.default`) are
    `deriving`-machinery, not user dead-code. -/
def hasInstanceComponent : Name → Bool
  | .str p s => "inst".isPrefixOf s || hasInstanceComponent p
  | .num p _ => hasInstanceComponent p
  | .anonymous => false

/-- A real user declaration (theorem/def/opaque/axiom) — not auto-generated,
    not an instance internal, not a structure projection. -/
def isRealDecl (env : Environment) (n : Name) : Bool :=
  !hasInstanceComponent n
  && !env.isProjectionFn n
  && (env.find? n).any fun ci =>
       match ci with
       | .thmInfo _ | .defnInfo _ | .axiomInfo _ | .opaqueInfo _ => true
       | _ => false

/-- Load the allow-list (fully-qualified names, one per line; `#` comments). -/
def loadAllow : IO NameSet := do
  let path := "tools/deadcode-allow.txt"
  if !(← System.FilePath.pathExists path) then return {}
  let txt ← IO.FS.readFile path
  let mut s : NameSet := {}
  for line in txt.splitOn "\n" do
    let l := (line.takeWhile (· != '#')).trimAscii
    if !l.isEmpty then s := s.insert l.toName
  return s

/-- The advisory report, over the imported environment. -/
def report : CommandElabM Unit := do
  let env ← getEnv
  let allow ← loadAllow
  let live := reachable env
  let mut dead : Array (Name × Name) := #[]
  for (n, _) in env.const2ModIdx.toList do
    if inBangModule env n && isRealDecl env n && !live.contains n && !allow.contains n then
      if !(← liftCoreM (isAutoDecl n)) then
        if let some m := env.getModuleFor? n then
          dead := dead.push (m, n)
  dead := dead.qsort fun a b =>
    a.1.toString < b.1.toString || (a.1 == b.1 && a.2.toString < b.2.toString)
  IO.println s!"── dead-code (advisory) — Bang.* decls unreachable from {roots.length} roots ──"
  if dead.isEmpty then
    IO.println "  none — every Bang.* declaration is reachable (or allow-listed)."
  else
    IO.println s!"  {dead.size} unreachable declaration(s):"
    for (m, n) in dead do
      IO.println s!"    {m}  ::  {n}"
    IO.println ""
    IO.println "  Each is EITHER a genuine orphan (delete it) OR an intentional park"
    IO.println "  (add to tools/deadcode-allow.txt with a reason). Advisory — not a gate."

end Bang.Tools.DeadCode

#eval Bang.Tools.DeadCode.report
