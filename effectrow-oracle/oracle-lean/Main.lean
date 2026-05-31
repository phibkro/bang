import Bang.EffectRow
import Bang.EvalJson
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

  {"op":"eval","fuel":N,"expr":EXPR}         -> RESULT   (the bigger oracle, ADR-0008)
  {"op":"exec","expr":EXPR}                  -> RESULT   (calculated machine, ADR-0009;
                                                          arithmetic + let/var)
  {"op":"execho","fuel":N,"expr":EXPR}       -> RESULT   (calculated HO machine, ADR-0010;
                                                          + lam/app, CBV; proven)
  {"op":"execcbn","fuel":N,"expr":EXPR}      -> RESULT   (calculated CBN machine; + thunk/force,
                                                          call-by-name; matches Bang.Eval)
  {"op":"evaleff"/"execeff",…}               -> OUTCOME  (Throws: reference / calculated, ADR-0011)
  {"op":"evalst"/"execst",…}                 -> {value,state}  (State: reference / calculated, ADR-0011)
  {"op":"evalcbneff"/"execcbneff","fuel":N,"expr":EXPR}
                                             -> OUTCOME  (Throws over the CBN closure core:
                                                          reference / calculated, ADR-0012)
  {"op":"evalcbnst"/"execcbnst","fuel":N,"expr":EXPR}
                                             -> {value,state}  (State over the CBN closure core:
                                                          reference / calculated, ADR-0013)
  {"op":"evalcbneffst"/"execcbneffst","fuel":N,"expr":EXPR}
                                             -> OUTCOME+state  (Throws + State together in one
                                                          machine: reference / calculated, ADR-0014)
  {"op":"execreify","fuel":N,"expr":EXPR}    -> {ok,value}  (reification machine: multi-shot /
                                                          non-tail handlers, ADR-0015; cross-checked
                                                          vs an independent TS CPS interpreter)
  EXPR/RESULT wire format: see Bang/EvalJson.lean
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
  | "eval" =>
      -- the bigger oracle: drive the definitional interpreter (ADR-0008)
      Bang.EvalJson.evalRequest j
  | "exec" =>
      -- the CALCULATED machine: compile + run on the verified stack VM (ADR-0009)
      Bang.EvalJson.execRequest j
  | "execho" =>
      -- the CALCULATED higher-order machine: closures, CBV (ADR-0010)
      Bang.EvalJson.execHORequest j
  | "execcbn" =>
      -- the CALCULATED call-by-name machine: thunk/force, matches Bang.Eval
      Bang.EvalJson.execCBNRequest j
  | "evaleff" =>
      -- the effect reference semantics (total Outcome)
      Bang.EvalJson.evalEffRequest j
  | "execeff" =>
      -- the CALCULATED handler machine: general handlers, Throws (K3)
      Bang.EvalJson.execEffRequest j
  | "evalst" =>
      -- the State reference semantics (total, threaded register)
      Bang.EvalJson.evalStRequest j
  | "execst" =>
      -- the CALCULATED State machine: get/put/runState (K3)
      Bang.EvalJson.execStRequest j
  | "evalcbneff" =>
      -- effects over the CBN closure core: reference semantics (Throws, K3)
      Bang.EvalJson.evalCBNEffRequest j
  | "execcbneff" =>
      -- the CALCULATED CBN+Throws machine: re-throw at the meta-call boundary (ADR-0012)
      Bang.EvalJson.execCBNEffRequest j
  | "evalcbnst" =>
      -- State over the CBN closure core: reference semantics (ADR-0013)
      Bang.EvalJson.evalCBNStRequest j
  | "execcbnst" =>
      -- the CALCULATED CBN+State machine: register threaded through nested meta-runs (ADR-0013)
      Bang.EvalJson.execCBNStRequest j
  | "evalcbneffst" =>
      -- Throws + State together over the CBN closure core: reference semantics (ADR-0014)
      Bang.EvalJson.evalCBNEffStRequest j
  | "execcbneffst" =>
      -- the CALCULATED CBN + Throws + State machine: handler stack + register at once (ADR-0014)
      Bang.EvalJson.execCBNEffStRequest j
  | "execreify" =>
      -- the CALCULATED reification machine: multi-shot / non-tail handlers (ADR-0015);
      -- cross-checked against an independent TS CPS interpreter (no in-Lean reference)
      Bang.EvalJson.execReifyRequest j
  | other => throw s!"unknown op {other}"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then pure ()            -- EOF (a blank line is "\n", not "")
  else
    let t := line.trimAscii.toString    -- `String.trim` is deprecated in this pin
    if t ≠ "" then
      match handle t with
      -- MUST flush: Lean block-buffers stdout over a pipe, so without an explicit
      -- flush the long-lived differential harness starves (its reader never sees
      -- the reply line) and every query times out. One response per line, flushed.
      | .ok j    => stdout.putStrLn j.compress; stdout.flush
      | .error e => IO.eprintln s!"error: {e}"
    loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
