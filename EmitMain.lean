/-
  EmitMain.lean — the ◊5.5 rung-1 SPIKE runner (LEAF exe, outside the `Bang.+` glob).
  ─────────────────────────────────────────────────────────────────────────────────
  For each pure sample program it: (1) emits the `.wat` (via `Bang.WasmEmit.emitModule`)
  and writes it to a file; (2) runs the kernel oracle `Source.eval` on the SAME `Comp`
  and prints the resulting value. The caller (`tools/emit-rung1-diff.sh`) then runs the
  `.wat` on `wasmtime` and diffs the two — the first time bang output executes outside Lean.

  WHY a compiled exe (not `#eval`): `Source.eval`'s fuel recursion does NOT reduce reliably
  under `#eval`/`lake env lean` (repo lesson `lean-eval-reliable-only-compiled`). A `lake exe`
  is COMPILED, so the oracle runs correctly. (The emitter is pure string-building and would be
  `#eval`-safe, but co-locating both sides in one compiled exe keeps the diff honest.)

  Usage: `lake exe emit-rung1 <outdir>` — writes <outdir>/progN.wat and prints oracle values.
-/
import Bang.Backend.WasmEmit
import Bang.Backend.AbstractMachine

open Bang Bang.WasmEmit

/-- Render a kernel `Source.eval` result's integer payload for the diff (rung-1 = i64 arithmetic). -/
def oracleInt (M : Comp) : String :=
  match Source.eval 1000 M with
  | .done (.vint n) => toString n
  | .done _         => "NON-INT-VALUE"
  | _               => "ORACLE-DIVERGED-OR-STUCK"

/-- One sample: name, the `Comp`, and a human description. -/
structure Sample where
  name : String
  prog : Comp
  desc : String

def samples : List Sample :=
  [ ⟨"prog0", prog0, "1 + 2"⟩
  , ⟨"prog1", prog1, "let x = 1 + 2 in x * 3"⟩
  , ⟨"prog2", prog2, "let x = 5 in x + 10"⟩
  , ⟨"prog3", prog3, "let x = 2*3 in let y = x+4 in y-1"⟩ ]

def main (args : List String) : IO Unit := do
  let outdir := args.headD "."
  for s in samples do
    match emitModule s.prog with
    | .unsup r => IO.println s!"{s.name}: REFUSED — {r}"
    | .ok wat =>
        let path := s!"{outdir}/{s.name}.wat"
        IO.FS.writeFile path wat
        IO.println s!"{s.name}  ({s.desc})"
        IO.println s!"    wat:    {path}"
        IO.println s!"    oracle: Source.eval = {oracleInt s.prog}"
