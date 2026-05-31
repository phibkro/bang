// calc-ho.test.ts -- the calculated HIGHER-ORDER machine vs the reference `eval`.
//
// K2 increment 3 (ADR-0010): `Bang/CalcHO.lean` calculates a CBV closure machine
// from `eval`. Its Lean equivalence proof is still pending (shipped as `sorry`
// with a plan), so THIS differential test is the standing guarantee
// (invariant 1): the calculated machine (`execho` op) must agree with the
// definitional interpreter (`eval` op) on every program here.
//
// Programs are pure and total, so CBV (the machine) and CBN (`Bang.Eval`) agree
// on the value -- closures, capture, and higher-order application included.

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fc from "fast-check";
import { Oracle } from "../src/oracle-client.js";
import { type Expr, lit, binop, v, lam, app, letE } from "../src/ast.js";

const ORACLE_EXE = process.env.ORACLE_EXE ?? "../oracle-lean/.lake/build/bin/oracle";
const FUEL = 1_000_000;

async function intOf(p: Promise<{ ok: boolean; value?: { v: string; n?: number } }>): Promise<number | null> {
  const r = await p;
  return r.ok && r.value?.v === "int" ? r.value.n! : null;
}

// total int-valued higher-order programs: arithmetic, let, and the application
// of a freshly-bound unary lambda (whose body may capture outer vars + arithmetic
// on its parameter). Guarantees closed, well-scoped, int-valued, terminating.
function arbHO(): fc.Arbitrary<Expr> {
  const leaf = (vars: string[]): fc.Arbitrary<Expr> =>
    vars.length === 0
      ? fc.integer({ min: -9, max: 9 }).map(lit)
      : fc.oneof(fc.integer({ min: -9, max: 9 }).map(lit), fc.constantFrom(...vars).map(v));
  const go = (depth: number, vars: string[]): fc.Arbitrary<Expr> => {
    if (depth <= 0) return leaf(vars);
    const sub = () => go(depth - 1, vars);
    return fc.oneof(
      { weight: 1, arbitrary: leaf(vars) },
      { weight: 2, arbitrary: fc.tuple(fc.constantFrom("+", "*"), sub(), sub())
          .map(([op, a, b]) => binop(op, a, b)) },
      { weight: 1, arbitrary: (() => {                       // let x = e1 in e2
          const n = `x${depth}`;
          return fc.tuple(go(depth - 1, vars), go(depth - 1, [...vars, n])).map(([e1, e2]) => letE(n, e1, e2));
        })() },
      { weight: 2, arbitrary: (() => {                       // (λp. body) arg  -- closure + capture
          const p = `p${depth}`;
          return fc.tuple(go(depth - 1, [...vars, p]), go(depth - 1, vars))
            .map(([body, arg]) => app(lam(p, body), arg));
        })() },
    );
  };
  return go(3, []);
}

describe("calculated HO machine (execho) vs reference eval -- closures, CBV", () => {
  let oracle: Oracle;
  beforeAll(() => { oracle = new Oracle(ORACLE_EXE); });
  afterAll(() => { oracle?.close(); });

  const I = (x: string) => v(x);
  it.each([
    { name: "identity applied", p: app(lam("x", I("x")), lit(5)), want: 5 },
    { name: "(λx. x+x) 21", p: app(lam("x", binop("+", I("x"), I("x"))), lit(21)), want: 42 },
    { name: "const captures x: ((λx.λy.x) 7) 9", p: app(app(lam("x", lam("y", I("x"))), lit(7)), lit(9)), want: 7 },
    { name: "let-bound closure reused", // let f = λx. x*2 in f 10 + f 20 = 60
      p: letE("f", lam("x", binop("*", I("x"), lit(2))),
              binop("+", app(I("f"), lit(10)), app(I("f"), lit(20)))), want: 60 },
    { name: "higher-order arg: (λf. f 10) (λx. x*3)",
      p: app(lam("f", app(I("f"), lit(10))), lam("x", binop("*", I("x"), lit(3)))), want: 30 },
    { name: "closure captures an outer let var", // let k=5 in (λx. x+k) 8 = 13
      p: letE("k", lit(5), app(lam("x", binop("+", I("x"), I("k"))), lit(8))), want: 13 },
  ])("golden: execho === eval === expected -- $name", async ({ p, want }) => {
    const machine = await intOf(oracle.execHOProg(FUEL, p));
    const reference = await intOf(oracle.evalProg(FUEL, p));
    expect(machine).toBe(want);
    expect(reference).toBe(want);
  });

  it("agrees with eval on 500 random higher-order programs", async () => {
    await fc.assert(
      fc.asyncProperty(arbHO(), async (p) => {
        const machine = await intOf(oracle.execHOProg(FUEL, p));
        const reference = await intOf(oracle.evalProg(FUEL, p));
        return machine !== null && machine === reference;
      }),
      { numRuns: 500 },
    );
  });
});
