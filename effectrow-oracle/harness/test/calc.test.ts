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
import { type Expr, lit, binop } from "../src/ast.js";

const ORACLE_EXE = process.env.ORACLE_EXE ?? "../oracle-lean/.lake/build/bin/oracle";

// the int result of a program, or null if the oracle didn't return ok/int
async function intOf(p: Promise<{ ok: boolean; value?: { v: string; n?: number } }>): Promise<number | null> {
  const r = await p;
  return r.ok && r.value?.v === "int" ? r.value.n! : null;
}

// closed arithmetic programs over lit/+/*; values bounded to stay exact in f64
function arbArith(): fc.Arbitrary<Expr> {
  const go = (depth: number): fc.Arbitrary<Expr> =>
    depth <= 0
      ? fc.integer({ min: -9, max: 9 }).map(lit)
      : fc.oneof(
          { weight: 1, arbitrary: fc.integer({ min: -9, max: 9 }).map(lit) },
          { weight: 2, arbitrary: fc.tuple(fc.constantFrom("+", "*"), go(depth - 1), go(depth - 1))
              .map(([op, a, b]) => binop(op, a, b)) },
        );
  return go(3);
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
  ])("golden: exec === eval === expected ($want)", async ({ p, want }) => {
    const machine = await intOf(oracle.execProg(p));
    const reference = await intOf(oracle.evalProg(100_000, p));
    expect(machine).toBe(want);
    expect(reference).toBe(want);
  });

  it("agrees with eval on 500 random arithmetic programs", async () => {
    await fc.assert(
      fc.asyncProperty(arbArith(), async (p) => {
        const machine = await intOf(oracle.execProg(p));
        const reference = await intOf(oracle.evalProg(100_000, p));
        return machine !== null && machine === reference;
      }),
      { numRuns: 500 },
    );
  });
});
