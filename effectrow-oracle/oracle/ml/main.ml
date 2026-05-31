(* ============================================================================
   main.ml  --  UNVERIFIED glue (the `specs/ml` pattern from Everest).

   Speaks newline-delimited JSON on stdin/stdout, one query per line, so the
   TS harness can drive it with zero per-call process spawn. The verified brain
   is Bang_EffectRow; nothing here needs proving.

   Protocol (requests -> responses), all on a single line:

     {"op":"unify","fresh":N,"r1":ROW,"r2":ROW}
        -> {"ok":true,"subst":[[VAR,ROW],...]}  |  {"ok":false}
     {"op":"union","a":[..],"b":[..]}   -> {"labels":[..]}
     {"op":"canon","labels":[..]}       -> {"labels":[..]}
     {"op":"apply","fuel":N,"subst":[[VAR,ROW],...],"row":ROW} -> ROW

   where ROW = {"labels":[int,...],"tail": int | null }
   ============================================================================ *)

module B = Bang_EffectRow

(* ---- representation shims --------------------------------------------------
   With the PLACEHOLDER module, labels are plain int and these are identities.
   With the real F* extraction, label/rvar are Z.t; replace the two lines below
   with:   let z2i = Z.to_int   and   let i2z = Z.of_int
   and map them across the lists/options where noted. *)
let z2i (x : int) : int = x
let i2z (x : int) : int = x
let _ = i2z  (* silence unused warning under placeholder *)

let row_of_json (j : Yojson.Safe.t) : B.row =
  match j with
  | `Assoc fields ->
    let labels =
      match List.assoc_opt "labels" fields with
      | Some (`List xs) ->
        List.map (function `Int n -> i2z n | _ -> failwith "label not int") xs
      | _ -> failwith "missing labels"
    in
    let tail =
      match List.assoc_opt "tail" fields with
      | Some `Null | None -> None
      | Some (`Int n) -> Some (i2z n)
      | _ -> failwith "bad tail"
    in
    { B.labels = B.canon labels; B.tail = tail }
  | _ -> failwith "row not object"

let json_of_row (r : B.row) : Yojson.Safe.t =
  `Assoc [
    ("labels", `List (List.map (fun x -> `Int (z2i x)) r.B.labels));
    ("tail", (match r.B.tail with None -> `Null | Some v -> `Int (z2i v)));
  ]

let json_of_subst (s : (int * B.row) list) : Yojson.Safe.t =
  `List (List.map (fun (v, r) -> `List [ `Int (z2i v); json_of_row r ]) s)

let subst_of_json (j : Yojson.Safe.t) : (int * B.row) list =
  match j with
  | `List xs ->
    List.map (function
      | `List [ `Int v; rj ] -> (i2z v, row_of_json rj)
      | _ -> failwith "bad binding") xs
  | _ -> failwith "subst not list"

let labels_of_json (j : Yojson.Safe.t) : int list =
  match j with
  | `List xs -> List.map (function `Int n -> i2z n | _ -> failwith "not int") xs
  | _ -> failwith "labels not list"

let field f fields = List.assoc f fields
let int_field f fields = match field f fields with `Int n -> n | _ -> failwith "not int"

let handle (line : string) : string =
  let j = Yojson.Safe.from_string line in
  let fields = match j with `Assoc fs -> fs | _ -> failwith "request not object" in
  let resp =
    match field "op" fields with
    | `String "unify" ->
      let fresh = i2z (int_field "fresh" fields) in
      let r1 = row_of_json (field "r1" fields) in
      let r2 = row_of_json (field "r2" fields) in
      (match B.unify fresh r1 r2 with
       | None -> `Assoc [ ("ok", `Bool false) ]
       | Some s -> `Assoc [ ("ok", `Bool true); ("subst", json_of_subst s) ])
    | `String "union" ->
      let a = B.canon (labels_of_json (field "a" fields)) in
      let b = B.canon (labels_of_json (field "b" fields)) in
      `Assoc [ ("labels", `List (List.map (fun x -> `Int (z2i x)) (B.union a b))) ]
    | `String "canon" ->
      `Assoc [ ("labels",
                `List (List.map (fun x -> `Int (z2i x))
                         (B.canon (labels_of_json (field "labels" fields))))) ]
    | `String "apply" ->
      let fuel = int_field "fuel" fields in
      let s = subst_of_json (field "subst" fields) in
      let r = row_of_json (field "row" fields) in
      json_of_row (B.apply_r fuel s r)
    | _ -> failwith "unknown op"
  in
  Yojson.Safe.to_string resp

let () =
  try
    while true do
      let line = input_line stdin in
      if String.trim line <> "" then (print_string (handle line); print_newline ();
                                      flush stdout)
    done
  with End_of_file -> ()
