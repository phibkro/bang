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

/-- The `valPretty`/`asString` convention (Main.lean:120,130) replicated for the harness oracle: the
readback exe (`--print` mode) must produce EXACTLY this text. Kept in lockstep with Main.lean; the
GC-emitter's `renderPreamble` is the wasm image of the SAME grammar. -/
partial def oracleAsString : Val → Option String
  | .fold (.inl .vunit) => some ""
  | .fold (.inr (.pair (.fold (.vint cp)) rest)) =>
      (oracleAsString rest).map (fun s => String.singleton (Char.ofNat cp.toNat) ++ s)
  | _ => none

partial def oracleValPretty : Val → String
  | .vunit      => "()"
  | .vint n     => toString n
  | .vvar i     => s!"#{i}"
  | .vcap n l   => s!"<cap {n}@{l}>"
  | .vthunk _   => "<thunk>"
  | .inl v      => s!"inl {oracleValPretty v}"
  | .inr v      => s!"inr {oracleValPretty v}"
  | .pair a b   => s!"({oracleValPretty a}, {oracleValPretty b})"
  | .fold v     => match oracleAsString (.fold v) with
                   | some s => if s.isEmpty then s!"fold {oracleValPretty v}" else s
                   | none   => s!"fold {oracleValPretty v}"

/-- The full-shape oracle: `Source.eval`'s result rendered with `valPretty` — the SAME text
`bang run` (and `expected.txt`) carries, so the `_start` readback module's stdout diffs against it. -/
def oraclePretty (M : Comp) : String :=
  match Source.eval 100000000 M with
  | .done v => oracleValPretty v
  | _       => "ORACLE-DIVERGED-OR-STUCK"

def main (args : List String) : IO Unit := do
  match args with
  | "--shape" :: file :: _ =>
      let src ← IO.FS.readFile file
      match lowerEntry src with
      | .error m => IO.println s!"LOWER-ERROR: {m}"
      | .ok c => IO.println (Bang.ProofExport.showComp c)
  | "--print" :: file :: rest =>
      -- READBACK mode (rung-5 Part 1): full-shape oracle + a WASI `_start` module whose stdout is
      -- `valPretty (Source.eval M)` (byte-for-byte the expected.txt). Harness diffs the two.
      let src ← IO.FS.readFile file
      match lowerEntry src with
      | .error m => IO.println s!"LOWER-ERROR: {m}"
      | .ok c =>
          IO.println s!"oracle: valPretty = {oraclePretty c}"
          match Bang.WasmEmit.emitModuleGCPrint c with
          | .unsup r => IO.println s!"EMIT-REFUSED: {r}"
          | .ok wat =>
              match rest with
              | out :: _ => do IO.FS.writeFile out wat; IO.println s!"wat written: {out}"
              | [] => IO.println wat
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
  | [] => IO.println "usage: rung4-shape [--print|--shape] <file.bang> [<out.wat>]"
