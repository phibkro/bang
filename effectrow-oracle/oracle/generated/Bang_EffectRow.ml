(* ============================================================================
   Bang_EffectRow.ml  --  PLACEHOLDER / REFERENCE IMPLEMENTATION

   This file stands in for the output of `fstar.exe --codegen OCaml`. It lets
   the oracle build and run BEFORE you have the F* toolchain set up, and it
   mirrors oracle/src/Bang.EffectRow.fst line for line.

   Once you can extract, run `make -C oracle extract`, which OVERWRITES this
   file with the verified extraction. The two should be observationally
   identical; in fact diffing the behaviour of this placeholder against the
   extracted module is a free fourth differential check.

   Representation note: the real extraction represents `nat` as Z.t (zarith).
   This placeholder uses plain `int` for clarity. When you swap in the real
   extraction, the only thing main.ml needs are the i2z/z2i shims marked there.
   ============================================================================ *)

type label = int
type rvar  = int
type row   = { labels : label list; tail : rvar option }

let rec mem (x : label) (l : label list) : bool =
  match l with [] -> false | h :: t -> x = h || mem x t

let rec insert (x : label) (l : label list) : label list =
  match l with
  | [] -> [x]
  | h :: t ->
    if x < h then x :: h :: t
    else if x = h then h :: t          (* idempotence *)
    else h :: insert x t

let rec union (a : label list) (b : label list) : label list =
  match a with [] -> b | x :: t -> insert x (union t b)

let rec diff (a : label list) (b : label list) : label list =
  match a with
  | [] -> []
  | x :: t -> if mem x b then diff t b else insert x (diff t b)

let canon (l : label list) : label list = union l []

let subset (a : label list) (b : label list) : bool =
  List.for_all (fun x -> mem x b) a

(* on canonical rows this is just structural equality, but we keep the
   extensional version for safety / debugging *)
let row_eq (a : label list) (b : label list) : bool =
  subset a b && subset b a

let rec lookup (r : rvar) (s : (rvar * row) list) : row option =
  match s with
  | [] -> None
  | (k, v) :: t -> if k = r then Some v else lookup r t

let rec apply_r (fuel : int) (s : (rvar * row) list) (r : row) : row =
  match r.tail with
  | None -> r
  | Some v ->
    if fuel <= 0 then r
    else (match lookup v s with
          | None -> r
          | Some r' ->
            let rr = apply_r (fuel - 1) s r' in
            { labels = union r.labels rr.labels; tail = rr.tail })

let unify (fresh : rvar) (r1 : row) (r2 : row) : (rvar * row) list option =
  match r1.tail, r2.tail with
  | None, None ->
    if r1.labels = r2.labels then Some [] else None
  | Some v1, None ->
    if subset r1.labels r2.labels
    then Some [ (v1, { labels = diff r2.labels r1.labels; tail = None }) ]
    else None
  | None, Some v2 ->
    if subset r2.labels r1.labels
    then Some [ (v2, { labels = diff r1.labels r2.labels; tail = None }) ]
    else None
  | Some v1, Some v2 ->
    if v1 = v2 then (if r1.labels = r2.labels then Some [] else None)
    else
      let only2 = diff r2.labels r1.labels in
      let only1 = diff r1.labels r2.labels in
      Some [ (v1, { labels = only2; tail = Some fresh });
             (v2, { labels = only1; tail = Some fresh }) ]
