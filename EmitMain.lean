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

/-- The 4 hand-picked rung-1 samples (arithmetic + let-nesting), kept as regression anchors. -/
def handSamples : List Sample :=
  [ ⟨"prog0", prog0, "1 + 2"⟩
  , ⟨"prog1", prog1, "let x = 1 + 2 in x * 3"⟩
  , ⟨"prog2", prog2, "let x = 5 in x + 10"⟩
  , ⟨"prog3", prog3, "let x = 2*3 in let y = x+4 in y-1"⟩ ]

/-- Rung-1.5 hand-picked samples exercising the NEW arms: guarded div (incl. `/0 = 0`), and the
comparison + case-on-bool `if` pattern. These are the load-bearing regression witnesses. -/
def rung15Samples : List Sample :=
  -- guarded division: normal, and the div-by-zero the kernel makes total (a/0 = 0).
  [ ⟨"div0", .binop .div (.vint 10) (.vint 2), "10 / 2  ⇒ 5"⟩
  , ⟨"div1", .binop .div (.vint 7) (.vint 0), "7 / 0  ⇒ 0 (kernel total div)"⟩
  , ⟨"div2", .letC (.binop .sub (.vint 3) (.vint 3)) (.binop .div (.vint 100) (.vvar 0)),
             "let d = 3-3 in 100 / d  ⇒ 0 (dynamic zero divisor)"⟩
  -- comparison + case-on-bool = if-then-else:  if a<b then E₂ else E₁.
  -- boolVal false=inl→N₁(else), true=inr→N₂(then).
  , ⟨"if0", .letC (.binop .lt (.vint 1) (.vint 2)) (.case (.vvar 0) (.ret (.vint 100)) (.ret (.vint 200))),
            "if 1<2 then 200 else 100  ⇒ 200"⟩
  , ⟨"if1", .letC (.binop .lt (.vint 5) (.vint 2)) (.case (.vvar 0) (.ret (.vint 100)) (.ret (.vint 200))),
            "if 5<2 then 200 else 100  ⇒ 100"⟩
  , ⟨"if2", .letC (.binop .eq (.vint 4) (.vint 4)) (.case (.vvar 0) (.binop .add (.vint 1) (.vint 1)) (.binop .mul (.vint 3) (.vint 3))),
            "if 4==4 then 3*3 else 1+1  ⇒ 9"⟩
    -- x is bound by the OUTER letC; inside a case branch it sits at de Bruijn index 2
    -- (index 0 = case unit payload, index 1 = the letC-bound boolVal, index 2 = x).
  , ⟨"if3", .letC (.binop .add (.vint 2) (.vint 3))
             (.letC (.binop .lt (.vvar 0) (.vint 4)) (.case (.vvar 0) (.ret (.vvar 2)) (.binop .mul (.vvar 2) (.vint 2)))),
            "let x=2+3 in if x<4 then x*2 else x  ⇒ 5 (x=5, 5<4 false → inl/else = x)"⟩ ]

/-! ### Deterministic seed-indexed generator (rung-1.5 differential corpus)

A small linear-congruential PRNG drives a structured generator over the EMITTABLE fragment:
integer atoms (`vint`), in-scope variables (`vvar i`, `i < depth` — so every program is CLOSED),
arithmetic `binop` (add/sub/mul/div — div includes a deliberate zero-divisor branch so the guard
is exercised), `letC` nesting, and the fused comparison + case-on-bool `if`. No `Date.now`/IO
nondeterminism — a seed fully determines the program, so the corpus is reproducible and the
oracle (`Source.eval`) and engine (`wasmtime`) see the identical `Comp`. -/

/-- Linear-congruential step (Numerical Recipes constants) — a pure `Nat → Nat` stream. -/
def lcg (s : Nat) : Nat := (s * 1664525 + 1013904223) % 4294967296

/-- Next pseudo-random `Nat` in `[0, n)` and the advanced seed. `n = 0` guarded to 1. -/
def rnd (s : Nat) (n : Nat) : Nat × Nat :=
  let s' := lcg s
  (s' % (max n 1), s')

/-- A small integer atom (kept in a modest range so `i64` arithmetic never overflows in the
corpus — the unbounded-`Int`→i64 gap is out of this slice, see the probe note §4.1). -/
def genAtomInt (s : Nat) : Val × Nat :=
  let (k, s') := rnd s 21   -- 0..20
  (.vint (Int.ofNat k), s')

/-- An emittable atom `Val`: an in-scope variable (`vvar i`, `i < depth`) or an int literal.
When `depth = 0` (no vars in scope) it always yields an int, so the term stays CLOSED. -/
def genAtom (depth : Nat) (s : Nat) : Val × Nat :=
  if depth = 0 then genAtomInt s
  else
    let (pick, s1) := rnd s 3
    if pick = 0 then
      let (i, s2) := rnd s1 depth   -- 0 .. depth-1  ⇒ always in scope
      (.vvar i, s2)
    else genAtomInt s1

/-- An arithmetic `BinOp` (add/sub/mul/div), div weighted so the guard gets exercised. -/
def genArithOp (s : Nat) : BinOp × Nat :=
  let (k, s') := rnd s 4
  (match k with | 0 => .add | 1 => .sub | 2 => .mul | _ => .div, s')

/-- A leaf `Comp`: `ret atom`, or a single arithmetic `binop op atom atom` (div sometimes forced
to a literal-0 divisor so the guard is exercised). No recursion — the `fuel = 0` base case. -/
def genLeaf (depth : Nat) (s : Nat) : Comp × Nat :=
  let (shape, s1) := rnd s 2
  if shape = 0 then
    let (v, s2) := genAtom depth s1
    (.ret v, s2)
  else
    let (op, s2) := genArithOp s1
    let (a, s3) := genAtom depth s2
    let (b, s4) :=
      match op with
      | .div =>
          let (z, s3') := rnd s3 4
          if z = 0 then (Val.vint 0, s3') else genAtom depth s3'
      | _ => genAtom depth s3
    (.binop op a b, s4)

/-- Generate an emittable `Comp` at binder-`depth`, STRUCTURALLY recurring on `fuel` (matched as
`Nat.succ` so it is total — no `partial`, no inhabited-type obligation). `fuel = 0` is a leaf;
interior nodes add `letC` nesting and the fused comparison + case-on-bool `if`. -/
def genComp (depth : Nat) : Nat → Nat → Comp × Nat
  | 0, s => genLeaf depth s
  | Nat.succ f, s =>
    let (shape, s1) := rnd s 4
    match shape with
    | 0 =>   -- letC M N   (N under depth+1)
        let (m, s2) := genComp depth f s1
        let (n, s3) := genComp (depth + 1) f s2
        (.letC m n, s3)
    | 1 =>   -- fused if:  letC (binop cmp a b) (case (vvar 0) N₁ N₂)
        let (cmp, s2) := rnd s1 2
        let cmpOp : BinOp := if cmp = 0 then .lt else .eq
        let (a, s3) := genAtom depth s2
        let (b, s4) := genAtom depth s3
        -- Inside each branch the kernel has TWO extra binders over the outer scope: index 0 = the
        -- `case` unit payload, index 1 = the outer `letC`'s `boolVal`. Generate each branch at the
        -- OUTER `depth`, then `Comp.shiftFrom 0` TWICE lifts every var reference up by two binders —
        -- so a branch's outer var `i` becomes `i+2` (skipping BOTH the payload and boolVal slots),
        -- staying closed + reading neither unusable slot (exactly the emittable if-then-else shape).
        let (n1raw, s5) := genComp depth f s4
        let (n2raw, s6) := genComp depth f s5
        let n1 := Comp.shiftFrom 0 (Comp.shiftFrom 0 n1raw)
        let n2 := Comp.shiftFrom 0 (Comp.shiftFrom 0 n2raw)
        (.letC (.binop cmpOp a b) (.case (.vvar 0) n1 n2), s6)
    | _ =>   -- a leaf arithmetic binop (bias toward straight-line arithmetic)
        genLeaf depth s1

/-- The generated corpus: `count` seed-indexed emittable programs. Seed `i*2654435761+1`
(Knuth multiplicative hash) spreads consecutive indices across the LCG space. Each starts at
`depth = 0` (closed) with `fuel = 3` (bounded nesting). -/
def genCorpus (count : Nat) : List Sample :=
  (List.range count).map (fun i =>
    let seed := (i * 2654435761 + 1) % 4294967296
    let (prog, _) := genComp 0 3 seed
    ⟨s!"gen{i}", prog, s!"generated#{i} (seed {seed})"⟩)

/-- All samples run by the harness: hand anchors + rung-1.5 witnesses + ~50 generated. Only the
EMITTABLE ones are written; a refusal is reported but is NOT a differential failure (the generator
stays in-fragment by construction, so a refusal would flag a generator bug — printed loud). -/
def samples : List Sample := handSamples ++ rung15Samples ++ genCorpus 42

def main (args : List String) : IO Unit := do
  let outdir := args.headD "."
  let mut emitted := 0
  let mut refused := 0
  for s in samples do
    match emitModule s.prog with
    | .unsup r =>
        refused := refused + 1
        IO.println s!"{s.name}: REFUSED — {r}"
    | .ok wat =>
        emitted := emitted + 1
        let path := s!"{outdir}/{s.name}.wat"
        IO.FS.writeFile path wat
        IO.println s!"{s.name}  ({s.desc})"
        IO.println s!"    wat:    {path}"
        IO.println s!"    oracle: Source.eval = {oracleInt s.prog}"
  IO.println s!"EMITTED_COUNT {emitted}"
  IO.println s!"REFUSED_COUNT {refused}"
