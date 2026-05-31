module Bang.EffectRow

(* ----------------------------------------------------------------------------
   bang-lang effect rows, modelled as IDEMPOTENT SETS of labels with an
   optional polymorphic tail. Union is the semilattice join (idempotent,
   commutative, associative, with empty as identity) -- the "monoid tier" of
   the Trinity framing, and the algebra Effect TS's R/E channels actually obey
   (dedup, order-insensitive).

   This module is the SPEC + ORACLE BRAIN. It extracts to OCaml (the
   first-class F* backend) and is consumed by the differential test harness.

   Honesty note (carried over from the design discussion): this is written to
   be faithful in shape and intent. The spots most likely to need a nudge
   through the checker are flagged with  (* NUDGE *).  The accompanying
   tools/selfcheck.mjs re-implements every function below a third time and
   checks the same laws empirically, so the *algorithm* is de-risked even
   before you wire up the F* toolchain.
   -------------------------------------------------------------------------- *)

open FStar.List.Tot

(* Real labels (State, Exn, Async, ...) are interned to nats at the harness
   boundary. The core only needs a strict total order; nat keeps proofs cheap. *)
type label = nat

(* ===========================================================================
   1. Canonical rows: strictly increasing list = sorted AND duplicate-free.
      This single invariant IS the semilattice normal form.
   =========================================================================== *)

let rec inc (l: list label) : bool =
  match l with
  | [] -> true
  | [_] -> true
  | x :: y :: tl -> x < y && inc (y :: tl)

type rowc = l: list label { inc l }

let rec mem (x: label) (l: list label) : bool =
  match l with
  | [] -> false
  | h :: t -> x = h || mem x t

let rec insert (x: label) (l: list label) : Tot (list label) (decreases l) =
  match l with
  | [] -> [x]
  | h :: t ->
    if x < h then x :: h :: t
    else if x = h then h :: t            (* idempotence: drop the duplicate *)
    else h :: insert x t

let rec union (a b: list label) : Tot (list label) (decreases a) =
  match a with
  | [] -> b
  | x :: t -> insert x (union t b)

let rec diff (a b: list label) : Tot (list label) (decreases a) =
  match a with
  | [] -> []
  | x :: t -> if mem x b then diff t b else insert x (diff t b)

let subset (a b: list label) : bool = for_all (fun x -> mem x b) a

(* Semantic (extensional) equality of rows = same membership. *)
let row_eq (a b: list label) : prop = forall (x: label). mem x a == mem x b

(* ===========================================================================
   2. Lemmas that make the oracle trustworthy.
      insert/union preserve canonicity; union_mem links syntax to semantics;
      canon_unique is the KEYSTONE that collapses set-equality to list-equality.
   =========================================================================== *)

let rec insert_mem (x: label) (l: list label) (y: label)
  : Lemma (mem y (insert x l) == (y = x || mem y l)) (decreases l) =
  match l with
  | [] -> ()
  | h :: t -> if x < h then () else if x = h then () else insert_mem x t y

let rec insert_inc (x: label) (l: list label)
  : Lemma (requires inc l) (ensures inc (insert x l)) (decreases l) =
  match l with
  | [] -> ()
  | [_] -> ()
  | h1 :: h2 :: t ->
    if x < h1 then ()
    else if x = h1 then ()
    else (insert_inc x (h2 :: t);
          (* NUDGE: head-ordering after insert may need insert_head_lemma *)
          ())

let rec union_inc (a b: list label)
  : Lemma (requires inc a /\ inc b) (ensures inc (union a b)) (decreases a) =
  match a with
  | [] -> ()
  | x :: t ->
    (* inc (x::t) ==> inc t *)
    union_inc t b;
    insert_inc x (union t b)

let rec union_mem (a b: list label) (x: label)
  : Lemma (mem x (union a b) == (mem x a || mem x b)) (decreases a) =
  match a with
  | [] -> ()
  | h :: t ->
    union_mem t b x;
    insert_mem h (union t b) x

(* KEYSTONE: on canonical rows, extensional equality collapses to syntactic
   equality. This is what lets the oracle decide row-equality by (=) on lists.
   Proof sketch: induction on both lists; inc rules out the mismatch cases
   because the smallest element is forced to agree.
   NUDGE: this is the fiddliest one. If SMT stalls, introduce a helper
   `min_mem` lemma (the head of a canonical list is its unique minimum) and
   case on whether the heads are equal / which is smaller. *)
let rec canon_unique (a b: rowc)
  : Lemma (requires row_eq a b) (ensures a == b) (decreases a) =
  match a, b with
  | [], [] -> ()
  | [], (y :: _) ->
    assert (mem y a == mem y b)            (* mem y b = true, mem y a = false: contradiction *)
  | (x :: _), [] ->
    assert (mem x a == mem x b)
  | x :: ta, y :: tb ->
    (* heads are each the unique minimum of their (canonical) list, and
       row_eq forces the minima to coincide, hence x = y, then recurse. *)
    assert (mem x a == mem x b);
    assert (mem y a == mem y b);
    // x = y forced; then row_eq ta tb forced by inc (no element < head reappears)
    canon_unique ta tb

(* ===========================================================================
   3. Open rows + the Remy/Pottier-style unifier specialised to set-rows.
   =========================================================================== *)

type rvar = nat

type row = { labels: rowc; tail: option rvar }

type binding = rvar * row
type subst = list binding

let rec lookup (r: rvar) (s: subst) : Tot (option row) (decreases s) =
  match s with
  | [] -> None
  | (k, v) :: t -> if k = r then Some v else lookup r t

(* Apply a substitution to a row. Fuel guarantees termination even if a
   (malformed) substitution were cyclic; well-formed oracle output is acyclic
   and resolves within fuel = length s + 1. *)
let rec applyR (fuel: nat) (s: subst) (r: row) : Tot row (decreases fuel) =
  match r.tail with
  | None -> r
  | Some v ->
    if fuel = 0 then r
    else match lookup v s with
         | None -> r
         | Some r' ->
           let rr = applyR (fuel - 1) s r' in
           union_inc r.labels rr.labels;            (* keep labels canonical *)
           { labels = union r.labels rr.labels; tail = rr.tail }

(* The unifier. Returns a substitution that makes the two rows denote the same
   set and agree on tail, or None.

   closed/closed : succeed (empty subst) iff label sets equal
   open/closed   : closed side can't grow, so the open side's fixed labels must
                   be a subset; bind the open tail to the missing labels, closed.
   open/open     : one fresh tail var; each tail absorbs the other side's
                   exclusive labels plus the shared fresh tail. *)
let unify (fresh: rvar) (r1 r2: row) : option subst =
  match r1.tail, r2.tail with
  | None, None ->
    if r1.labels = r2.labels then Some [] else None

  | Some v1, None ->
    if subset r1.labels r2.labels
    then (let extra = diff r2.labels r1.labels in
          Some [ (v1, { labels = extra; tail = None }) ])
    else None

  | None, Some v2 ->
    if subset r2.labels r1.labels
    then (let extra = diff r1.labels r2.labels in
          Some [ (v2, { labels = extra; tail = None }) ])
    else None

  | Some v1, Some v2 ->
    if v1 = v2 then
      (* same tail variable can't carry two different extensions *)
      (if r1.labels = r2.labels then Some [] else None)
    else
      let only2 = diff r2.labels r1.labels in   (* labels r1 is missing *)
      let only1 = diff r1.labels r2.labels in   (* labels r2 is missing *)
      Some [ (v1, { labels = only2; tail = Some fresh });
             (v2, { labels = only1; tail = Some fresh }) ]

(* SOUNDNESS: if unify says yes with substitution s, then applying s makes the
   two rows denote the same label set and agree on tail.
   This is the property an ORACLE needs: a sound oracle catches every case
   where the transpiler claims a unification that is actually wrong. We do NOT
   attempt to prove most-generality (principality) here -- ACI unification is
   finitary but not unitary, so MGU is deferred to the differential test.
   NUDGE: prove by case-split mirroring `unify`; each branch needs union_mem +
   the membership lemmas above. The open/open branch is the one to write first. *)
val unify_sound (fresh: rvar) (r1 r2: row) (s: subst)
  : Lemma (requires unify fresh r1 r2 == Some s)
          (ensures (let f = length s + 2 in
                    row_eq (applyR f s r1).labels (applyR f s r2).labels /\
                    (applyR f s r1).tail == (applyR f s r2).tail))
