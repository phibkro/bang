// eval.test.ts -- the differential harness for the `eval` oracle (ADR-0008).
//
//   1. golden programs: candidate(prog) === oracle(prog) === expected value
//   2. fuzz the pure arithmetic core: candidate vs the verified Lean oracle on
//      random closed expressions, compared by RESULT (skipping the rare
//      out-of-fuel case, where the two fuel accountings legitimately differ).

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fc from "fast-check";
import { Oracle } from "../src/oracle-client.js";
import { evalCandidate } from "../src/eval-candidate.js";
import { type Expr, type RunResult, type Value, lit, v, letE, ifE, binop } from "../src/ast.js";
import { GOLDENS } from "./eval-programs.js";

const ORACLE_EXE = process.env.ORACLE_EXE ?? "../oracle-lean/.lake/build/bin/oracle";
const FUEL = 100_000;

// Canonical, key-order-independent rendering of a value (the oracle and the
// candidate emit object keys in different orders).
function canonVal(x: Value): unknown {
  switch (x.v) {
    case "int":  return ["int", x.n];
    case "con":  return ["con", x.c, x.args.map(canonVal)];
    default:     return [x.v];
  }
}

// Compare two results by observable outcome. `stuck` messages are wording, not
// behavior, so they are compared by reason only; everything else is exact.
function resultsAgree(a: RunResult, b: RunResult): boolean {
  if (a.ok !== b.ok) return false;
  if (a.ok && b.ok) return JSON.stringify(canonVal(a.value)) === JSON.stringify(canonVal(b.value));
  if (!a.ok && !b.ok) {
    if (a.reason !== b.reason) return false;
    if (a.reason === "uncaught" && b.reason === "uncaught")
      return a.label === b.label && a.effOp === b.effOp;
    return true; // stuck (ignore msg) / outOfFuel
  }
  return false;
}

describe("eval golden programs: candidate === oracle === expected", () => {
  let oracle: Oracle;
  beforeAll(() => { oracle = new Oracle(ORACLE_EXE); });
  afterAll(() => { oracle?.close(); });

  it.each(GOLDENS)("$name", async ({ prog, expect: want }) => {
    const mine = evalCandidate(FUEL, prog);
    const truth = await oracle.evalProg(FUEL, prog);
    expect(resultsAgree(mine, want), `candidate disagreed with expected: ${JSON.stringify(mine)}`).toBe(true);
    expect(resultsAgree(truth, want), `oracle disagreed with expected: ${JSON.stringify(truth)}`).toBe(true);
  });
});

// A generator for the pure arithmetic core (no effects -> never `stuck`):
// literals, +/-/*, `let`-bound variables, and `if (a<b)`. Variables only ever
// reference already-bound names, so every generated program is closed.
function arbExpr(): fc.Arbitrary<Expr> {
  const leaf = (vars: string[]): fc.Arbitrary<Expr> =>
    vars.length === 0
      ? fc.integer({ min: -50, max: 50 }).map(lit)
      : fc.oneof(fc.integer({ min: -50, max: 50 }).map(lit), fc.constantFrom(...vars).map(v));

  const go = (depth: number, vars: string[]): fc.Arbitrary<Expr> => {
    if (depth <= 0) return leaf(vars);
    const sub = () => go(depth - 1, vars);
    return fc.oneof(
      { weight: 1, arbitrary: leaf(vars) },
      { weight: 3, arbitrary: fc.tuple(fc.constantFrom("+", "-", "*"), sub(), sub())
          .map(([op, a, b]) => binop(op, a, b)) },
      { weight: 1, arbitrary: fc.tuple(sub(), sub(), sub(), sub())
          .map(([a, b, t, e]) => ifE(binop("<", a, b), t, e)) },
      { weight: 1, arbitrary: (() => {
          const name = `x${depth}`;
          return fc.tuple(go(depth - 1, vars), go(depth - 1, [...vars, name]))
            .map(([e1, e2]) => letE(name, e1, e2));
        })() },
    );
  };
  return go(4, []);
}

describe("eval fuzz: candidate vs verified oracle on the pure arithmetic core", () => {
  let oracle: Oracle;
  beforeAll(() => { oracle = new Oracle(ORACLE_EXE); });
  afterAll(() => { oracle?.close(); });

  it("agrees on 500 random closed arithmetic programs", async () => {
    await fc.assert(
      fc.asyncProperty(arbExpr(), async (prog) => {
        const mine = evalCandidate(FUEL, prog);
        const truth = await oracle.evalProg(FUEL, prog);
        if (!mine.ok && mine.reason === "outOfFuel") return true;   // fuel accounting differs
        if (!truth.ok && truth.reason === "outOfFuel") return true;
        return resultsAgree(mine, truth);
      }),
      { numRuns: 500 },
    );
  });
});
