import Bang.EffectRow
import Lean.Data.Json

/-!
Oracle entry point. Speaks the SAME newline-delimited JSON protocol as the F*/
OCaml oracle (`oracle/ml/main.ml`), so `harness/` drives it with only the
`ORACLE_EXE` path changed. Lean compiles this to a native binary directly, so
there is no separate extraction/glue step.

  {"op":"unify","fresh":N,"r1":ROW,"r2":ROW} -> {"ok":true,"subst":[[V,ROW]..]} | {"ok":false}
  {"op":"union","a":[..],"b":[..]}           -> {"labels":[..]}
  {"op":"canon","labels":[..]}               -> {"labels":[..]}
  {"op":"apply","fuel":N,"subst":[[V,ROW]..],"row":ROW} -> ROW
  ROW = {"labels":[int..],"tail": int | null}
-/

open Lean Bang.EffectRow

/-- Sorted label list for serialisation (matches the OCaml oracle's output).
NUDGE: if `Finset.sort` instance resolution complains, `(s.toList).mergeSort (· ≤ ·)`
is an equivalent fallback. -/
-- NUDGE resolved: `Finset.sort`'s signature in this Lean/Mathlib pin takes the
-- Finset as the FIRST (explicit) argument and the order relation as an autoParam,
-- so the original `Finset.sort (· ≤ ·) s` no longer typechecks. Dot notation
-- `s.sort (· ≤ ·)` supplies the Finset first. (`Finset.toList` is noncomputable
-- in this pin and would break the executable; `Finset.sort` stays computable.)
def sortedLabels (s : RowC) : List Nat := s.sort (· ≤ ·)

def rowToJson (r : Row) : Json :=
  Json.mkObj
    [ ("labels", toJson (sortedLabels r.labels)),
      ("tail", match r.tail with | none => Json.null | some v => toJson v) ]

def substToJson (s : Subst) : Json :=
  Json.arr <| (s.map (fun (v, r) => Json.arr #[toJson v, rowToJson r])).toArray

def rowFromJson (j : Json) : Except String Row := do
  let labels ← j.getObjValAs? (Array Nat) "labels"
  let tail   ← j.getObjValAs? (Option Nat) "tail"
  pure { labels := labels.toList.toFinset, tail }

def substFromJson (j : Json) : Except String Subst := do
  let arr ← j.getArr?
  arr.toList.mapM fun bj => do
    let b ← bj.getArr?
    let v ← (b[0]!).getNat?
    let r ← rowFromJson (b[1]!)
    pure (v, r)

def handle (line : String) : Except String Json := do
  let j ← Json.parse line
  match ← j.getObjValAs? String "op" with
  | "unify" =>
      let fresh ← j.getObjValAs? Nat "fresh"
      let r1 ← rowFromJson (← j.getObjVal? "r1")
      let r2 ← rowFromJson (← j.getObjVal? "r2")
      match unify fresh r1 r2 with
      | none   => pure <| Json.mkObj [("ok", Json.bool false)]
      | some s => pure <| Json.mkObj [("ok", Json.bool true), ("subst", substToJson s)]
  | "union" =>
      let a ← j.getObjValAs? (Array Nat) "a"
      let b ← j.getObjValAs? (Array Nat) "b"
      let u := a.toList.toFinset ∪ b.toList.toFinset
      pure <| Json.mkObj [("labels", toJson (sortedLabels u))]
  | "canon" =>
      let l ← j.getObjValAs? (Array Nat) "labels"
      pure <| Json.mkObj [("labels", toJson (sortedLabels l.toList.toFinset))]
  | "apply" =>
      let fuel ← j.getObjValAs? Nat "fuel"
      let s ← substFromJson (← j.getObjVal? "subst")
      let r ← rowFromJson (← j.getObjVal? "row")
      pure <| rowToJson (applyR fuel s r)
  | other => throw s!"unknown op {other}"

partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then pure ()            -- EOF (a blank line is "\n", not "")
  else
    let t := line.trim
    if t ≠ "" then
      match handle t with
      | .ok j    => IO.println j.compress
      | .error e => IO.eprintln s!"error: {e}"
    loop stdin

def main : IO Unit := do
  loop (← IO.getStdin)
