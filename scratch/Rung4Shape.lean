/-
  scratch/Rung4Shape.lean — rung-4 emission runner + shape probe.
  Lowers a source .bang file to its kernel `Comp`, emits WasmGC via `emitModuleGC`, writes the
  `.wat`, and prints the `Source.eval` oracle value. The caller diffs the wasmtime run vs oracle.
  LEAF exe, not proof-bearing.

  Usage: `lake exe rung4-shape <file.bang> [<out.wat>]`
         `lake exe rung4-shape --shape <file.bang>`   (dump the Comp)
-/
import Bang.Frontend.TypeCheck
import Bang.Backend.AbstractMachine
import Bang.Backend.WasmEmit
import Bang.Witness.ProofExport

open Bang

/-- Lower a whole .bang source to a `Comp`, applying the ADR-0093 D5 entry rule (a `let main = …`
decl with no trailing body becomes the program's returned value — the SAME rule `bang run` applies
via `applyEntryRule`, so my probe matches the runner instead of the raw decl-fold's `ret 0`). -/
def lowerEntry (src : String) : Except String Comp := do
  let prog ← Bang.Surface.parseProg src
  let hasMain := prog.decls.any (fun d => match d with
    | .letD n _ _ | .letRecD n _ _ => n == "main"
    | _ => false)
  let prog := if hasMain && prog.isLibrary then { prog with body := Bang.Surface.Surf.var "main", isLibrary := false } else prog
  Bang.TypeCheck.checkAndLowerProg prog

def oracleInt (M : Comp) : String :=
  match Source.eval 100000000 M with
  | .done (.vint n) => toString n
  | .done _         => "NON-INT-VALUE"
  | _               => "ORACLE-DIVERGED-OR-STUCK"

def main (args : List String) : IO Unit := do
  match args with
  | "--shape" :: file :: _ =>
      let src ← IO.FS.readFile file
      match lowerEntry src with
      | .error m => IO.println s!"LOWER-ERROR: {m}"
      | .ok c => IO.println (Bang.ProofExport.showComp c)
  | file :: rest =>
      let src ← IO.FS.readFile file
      match lowerEntry src with
      | .error m => IO.println s!"LOWER-ERROR: {m}"
      | .ok c =>
          IO.println s!"oracle: Source.eval = {oracleInt c}"
          match Bang.WasmEmit.emitModuleGC c with
          | .unsup r => IO.println s!"EMIT-REFUSED: {r}"
          | .ok wat =>
              match rest with
              | out :: _ => do IO.FS.writeFile out wat; IO.println s!"wat written: {out}"
              | [] => IO.println wat
  | [] => IO.println "usage: rung4-shape <file.bang> [<out.wat>]"
