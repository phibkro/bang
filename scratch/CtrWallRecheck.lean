import Bang.Frontend.TypeCheck

/-! # PROBE (task #34, lane ctr): re-verify the ADR-0092 D3 / ADR-0095 D4 answer-grade wall on CURRENT main.

Three machine-checked questions, isolating exactly what the "wall" is post the term-measured LR rebuild,
Stage 6, and the LANDED Stage-7 surface (`1284c8e`).

RE1. THE SURFACE ACCEPTS a computing-but-pure clause body (`n * 10`). This is the tracer, `checkProg`-green.
     ⟹ the "wall" is NOT "no computing clause body type-checks at the surface". A PURE compute-then-return
        body already passes the surface gate — only an EFFECTFUL one hits the D4 diagnostic.

RE2. THE LOWERED KERNEL Comp of that same clause body is a `Comp.binop`-containing computation, NOT a
     `Comp.ret w`. So the kernel typed rule `HasClauses.cons` (which pattern-matches `(op, Comp.ret w)`)
     CANNOT type this clause list — the tracer's custom handler runs in the TESTED superset, diff-tested
     against `Source.eval`, NOT covered by the kernel `handleCustom`/`custom_program_safe` soundness.
     ⟹ the surface type-gate (`synthSC`) and the kernel soundness (`HasClauses`/`HasCTy`) are DIFFERENT
        layers joined by the stratification seam, not the same gate. The wall is a KERNEL-TYPING wall.

RE3. THE KERNEL WALL STILL STANDS: `HasCTy.binop_untypable` is live (no `HasCTy` rule for `Comp.binop`),
     so a lowered `binop`-containing clause body types at NO grade in the kernel — the GradeForkProbe
     finding (1) holds verbatim on today's code. -/

namespace Bang.CtrWallRecheck

open Bang Bang.Surface

-- RE1: the surface accepts the pure computing clause body (the tracer). checkProgRow-green (public proj).
#guard (match Bang.TypeCheck.checkProgRow
    "effect Net { fetch : Int -> Int } handle (net.fetch(1)) + (net.fetch(2)) with Net as net { fetch(n) => n * 10 }"
  with | .ok _ => true | .error _ => false)

-- RE1b: an EFFECTFUL clause body is REJECTED with the D4 diagnostic (naming ADR-0065 + Q27).
#guard (match Bang.TypeCheck.checkProgRow
    "effect Net { fetch : Int -> Int } handle net.fetch(1) with Net as net { fetch(n) => raise n }"
  with
  | .error m => (m.splitOn "ADR-0065").length > 1 && (m.splitOn "Q27").length > 1
  | .ok _ => false)

-- RE2: the lowered kernel Comp — inspect the custom clause body. Expect a `Comp.binop`-containing
-- computation, NOT `Comp.ret _`. We check by lowering and pattern-probing the handler clause list.
open Bang.TypeCheck in
#eval do
  let src := "effect Net { fetch : Int -> Int } handle (net.fetch(1)) + (net.fetch(2)) with Net as net { fetch(n) => n * 10 }"
  match Bang.Surface.parseProg src with
  | .error e => IO.println s!"RE2 parse error: {e}"
  | .ok prog =>
    match Bang.TypeCheck.checkAndLowerProg prog with
    | .error e => IO.println s!"RE2 lower error: {e}"
    | .ok c =>
      -- walk to the innermost Handler.custom clause list and report the head clause body's head constructor.
      let rec findCustom : Comp → Option (List (OpId × Comp))
        | .handle (.custom _ _ cls) _ => some cls
        | .letC a b => (findCustom a).orElse (fun _ => findCustom b)
        | .handle _ m => findCustom m
        | _ => none
      match findCustom c with
      | none => IO.println "RE2: no Handler.custom found (unexpected)"
      | some [] => IO.println "RE2: empty clause list (unexpected)"
      | some ((op, body) :: _) =>
        let head := match body with
          | .ret _     => "Comp.ret (VALUE — would satisfy HasClauses)"
          | .letC _ _  => "Comp.letC (COMPUTATION — HasClauses.cons CANNOT match)"
          | .binop _ _ _ => "Comp.binop (COMPUTATION — HasClauses.cons CANNOT match)"
          | _          => "other computation"
        IO.println s!"RE2: clause '{op}' body head = {head}"

end Bang.CtrWallRecheck
