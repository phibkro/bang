// calc.test.ts -- the calculated stack machine vs the reference `eval`.
//
// K2 increment 1 (ADR-0009): `Bang/Calc.lean` PROVES `exec (compile e []) =
// [eval e]` for the arithmetic kernel. This closes the other half of the loop
// operationally -- the calculated machine (`exec` op) agrees with the
// definitional interpreter (`eval` op) on the same programs:
//
//     machine  ==(Lean proof)==  denotational eval  ==(this test)==  operational eval
//
// Arithmetic only (lit, +, *), since that is what's been calculated so far.

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fc from "fast-check";
import { Oracle } from "../src/oracle-client.js";
import { type Expr, lit, binop, v, letE } from "../src/ast.js";

const ORACLE_EXE = process.env.ORACLE_EXE ?? "../oracle-lean/.lake/build/bin/oracle";

// the int result of a program, or null if the oracle didn't return ok/int
async function intOf(p: Promise<{ ok: boolean; value?: { v: string; n?: number } }>): Promise<number | null> {
  const r = await p;
  return r.ok && r.value?.v === "int" ? r.value.n! : null;
}

// closed programs over lit/+/*/let/var; values bounded to stay exact in f64.
// `let` only ever binds fresh names and `var` only references in-scope names, so
// every generated program is closed and well-scoped.
function arbProg(): fc.Arbitrary<Expr> {
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
      { weight: 1, arbitrary: (() => {
          const name = `x${depth}`;
          return fc.tuple(go(depth - 1, vars), go(depth - 1, [...vars, name]))
            .map(([e1, e2]) => letE(name, e1, e2));
        })() },
    );
  };
  return go(3, []);
}

describe("calculated machine (exec) vs reference eval -- arithmetic kernel", () => {
  let oracle: Oracle;
  beforeAll(() => { oracle = new Oracle(ORACLE_EXE); });
  afterAll(() => { oracle?.close(); });

  it.each([
    { p: lit(42), want: 42 },
    { p: lit(-7), want: -7 },
    { p: binop("+", lit(20), lit(22)), want: 42 },
    { p: binop("*", binop("+", lit(2), lit(3)), lit(4)), want: 20 },          // (2+3)*4
    { p: binop("+", binop("*", lit(6), lit(7)), lit(-2)), want: 40 },         // 6*7-2 via +(-2)
    { p: letE("x", lit(5), binop("+", v("x"), v("x"))), want: 10 },           // let x=5 in x+x
    // let x=3 in let y=4 in x*y + x  (nested binders, de Bruijn indices)
    { p: letE("x", lit(3), letE("y", lit(4),
        binop("+", binop("*", v("x"), v("y")), v("x")))), want: 15 },
    // shadowing: let x=1 in (let x=2 in x) + x  = 2 + 1 = 3
    { p: letE("x", lit(1), binop("+", letE("x", lit(2), v("x")), v("x"))), want: 3 },
  ])("golden: exec === eval === expected ($want)", async ({ p, want }) => {
    const machine = await intOf(oracle.execProg(p));
    const reference = await intOf(oracle.evalProg(100_000, p));
    expect(machine).toBe(want);
    expect(reference).toBe(want);
  });

  it("agrees with eval on 500 random arithmetic+let/var programs", async () => {
    await fc.assert(
      fc.asyncProperty(arbProg(), async (p) => {
        const machine = await intOf(oracle.execProg(p));
        const reference = await intOf(oracle.evalProg(100_000, p));
        return machine !== null && machine === reference;
      }),
      { numRuns: 500 },
    );
  });
});
