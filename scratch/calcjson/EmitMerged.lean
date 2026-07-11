/-
  scratch/calcjson/EmitMerged.lean — the calc/json EMIT-path probe.
  Mirrors Main.lean's resolve+merge (mergeModules) so the emitter sees the SAME flat merged `Comp`
  that `bang run` lowers — isolating the TRUE emit wall from the harness's missing module resolution.

  Usage: lake env lean --run scratch/calcjson/EmitMerged.lean <exampleDir> <mod1> <mod2> ... -- entry=main
  We hardcode the two corpus targets below instead (simpler, no arg parsing subtleties).
-/
import Bang.Frontend.Surface
import Bang.Frontend.TypeCheck
import Bang.Backend.AbstractMachine
import Bang.Backend.WasmEmit

open Bang

/-- Read + parse one module file, returning (name, Prog). -/
def loadMod (dir name : String) : IO (String × Surface.Prog) := do
  let src ← IO.FS.readFile s!"{dir}/{name}.bang"
  match Bang.Surface.parseProg src with
  | .error m => throw (IO.userError s!"parse {name}: {m}")
  | .ok p => pure (name, p)

/-- Apply the D5 entry rule (main-decl → body := var "main"). -/
def applyEntry (p : Surface.Prog) : Surface.Prog :=
  let hasMain := p.decls.any (fun d => match d with
    | .letD n _ _ | .letRecD n _ _ => n == "main"
    | _ => false)
  if hasMain && p.isLibrary then { p with body := Surface.Surf.var "main", isLibrary := false } else p

def probe (label dir : String) (depMods : List String) : IO Unit := do
  IO.println s!"═══════ {label} ═══════"
  -- resolved deps in dependency order (deps before dependents), then the entry `main`.
  let resolved ← depMods.mapM (loadMod dir)
  let (_, entry) ← loadMod dir "main"
  match Bang.TypeCheck.mergeModules resolved entry with
  | .error m => IO.println s!"MERGE-ERROR: {m}"
  | .ok merged =>
      let merged := applyEntry merged
      match Bang.TypeCheck.checkAndLowerProg merged with
      | .error m => IO.println s!"LOWER-ERROR: {m}"
      | .ok c =>
          IO.println "LOWER: ok"
          match Bang.WasmEmit.emitModuleGCPrint c with
          | .unsup r => IO.println s!"EMIT-REFUSED: {r}"
          | .ok wat => do
              IO.FS.writeFile s!"scratch/calcjson/{label}.wat" wat
              IO.println s!"EMIT: ok (wrote scratch/calcjson/{label}.wat)"

def main : IO Unit := do
  -- calc: Ast (leaf) · Lexer · Parser (imports Ast) · Eval (imports Ast) · Print (imports Ast)
  probe "CALC" "examples/calc" ["Ast", "Lexer", "Parser", "Eval", "Print"]
  -- json: Json (leaf) · Parse (imports Json) · Print (imports Json)
  probe "JSON" "examples/json" ["Json", "Parse", "Print"]
