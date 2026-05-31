// calc-cbn.test.ts -- the calculated CALL-BY-NAME machine vs the reference `eval`.
//
// K2 increment 4: `Bang/CalcCBN.lean` calculates a CBN closure machine with
// thunk/force. Unlike the CBV machine, `Bang.Eval` is *itself* call-by-name, so
// the calculated machine (`execcbn` op) must agree with it on EVERY program here
// -- including ones where call-by-name and call-by-value would differ (an unused,
// would-be-distinct argument that CBN never forces).

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fc from "fast-check";
import { Oracle } from "../src/oracle-client.js";
import { type Expr, lit, binop, v, lam, app, letE, thunk, force } from "../src/ast.js";

const ORACLE_EXE = process.env.ORACLE_EXE ?? "../oracle-lean/.lake/build/bin/oracle";
const FUEL = 1_000_000;

async function intOf(p: Promise<{ ok: boolean; value?: { v: string; n?: number } }>): Promise<number | null> {
  const r = await p;
  return r.ok && r.value?.v === "int" ? r.value.n! : null;
}

// total int-valued CBN programs. Strict positions (binop operands, the `force`
// argument) get forced; `let`/`app`/`thnk` introduce descriptions. Var reads in a
// strict position are forced by the surrounding op. Closed + well-scoped.
function arbCBN(): fc.Arbitrary<Expr> {
  const leaf = (vars: string[]): fc.Arbitrary<Expr> =>
    vars.length === 0
      ? fc.integer({ min: -9, max: 9 }).map(lit)
      : fc.oneof(fc.integer({ min: -9, max: 9 }).map(lit), fc.constantFrom(...vars).map((n) => force(v(n))));
  const go = (depth: number, vars: string[]): fc.Arbitrary<Expr> => {
    if (depth <= 0) return leaf(vars);
    const sub = () => go(depth - 1, vars);
    return fc.oneof(
      { weight: 1, arbitrary: leaf(vars) },
      { weight: 2, arbitrary: fc.tuple(fc.constantFrom("+", "*"), sub(), sub()).map(([o, a, b]) => binop(o, a, b)) },
      { weight: 1, arbitrary: fc.tuple(sub()).map(([e]) => force(thunk(e))) },     // $⟨e⟩ round-trip
      { weight: 1, arbitrary: (() => {                                             // let x = e1 in e2
          const n = `x${depth}`;
          return fc.tuple(sub(), go(depth - 1, [...vars, n])).map(([e1, e2]) => letE(n, e1, e2));
        })() },
      { weight: 2, arbitrary: (() => {                                             // (λp. body) arg
          const p = `p${depth}`;
          return fc.tuple(go(depth - 1, [...vars, p]), sub()).map(([body, arg]) => app(lam(p, body), arg));
        })() },
    );
  };
  return go(3, []);
}

describe("calculated CBN machine (execcbn) vs reference eval -- thunk/force", () => {
  let oracle: Oracle;
  beforeAll(() => { oracle = new Oracle(ORACLE_EXE); });
  afterAll(() => { oracle?.close(); });

  const fv = (x: string) => force(v(x));
  it.each([
    { name: "$(let x = 2+3 in $x)", p: force(letE("x", binop("+", lit(2), lit(3)), fv("x"))), want: 5 },
    { name: "$⟨4*5⟩ explicit thunk", p: force(thunk(binop("*", lit(4), lit(5)))), want: 20 },
    { name: "CBN laziness: (λx.7)(2*3), arg never forced",
      p: app(lam("x", lit(7)), binop("*", lit(2), lit(3))), want: 7 },
    { name: "let-bound thunk forced twice (call-by-name, recomputed)",
      p: letE("x", binop("+", lit(10), lit(11)), binop("+", fv("x"), fv("x"))), want: 42 },
    { name: "apply identity, force result: $((λx.$x) (3+4))",
      p: force(app(lam("x", fv("x")), binop("+", lit(3), lit(4)))), want: 7 },
    { name: "closure captures a lazy outer binding",
      p: letE("k", binop("+", lit(2), lit(3)), force(app(lam("x", binop("+", fv("x"), fv("k"))), lit(8)))), want: 13 },
  ])("golden: execcbn === eval === expected -- $name", async ({ p, want }) => {
    const machine = await intOf(oracle.execCBNProg(FUEL, p));
    const reference = await intOf(oracle.evalProg(FUEL, p));
    expect(machine).toBe(want);
    expect(reference).toBe(want);
  });

  it("agrees with eval on 500 random call-by-name programs", async () => {
    await fc.assert(
      fc.asyncProperty(arbCBN(), async (p) => {
        const machine = await intOf(oracle.execCBNProg(FUEL, p));
        const reference = await intOf(oracle.evalProg(FUEL, p));
        return machine !== null && machine === reference;
      }),
      { numRuns: 500 },
    );
  });
});
