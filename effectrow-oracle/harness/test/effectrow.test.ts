// effectrow.test.ts -- the differential harness.
//
// Two kinds of test:
//   1. property laws asserted on the TS reference (the same four laws the F*
//      side PROVES: idempotent commutative monoid = bounded semilattice)
//   2. the differential test: transpiler.unify vs the verified oracle, compared
//      by DENOTATION (see rowalg.sameResult), with shrunk counterexamples
//      frozen into a golden corpus.

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fc from "fast-check";
import { Oracle } from "../src/oracle-client.js";
import * as unify from "../src/transpiler.js";
import {
  canon, union, sameResult, rowEq, type Row, type Subst,
} from "../src/rowalg.js";
import GOLDEN from "./golden.json";

const ORACLE_EXE = process.env.ORACLE_EXE ?? "../oracle/_build/default/ml/main.exe";

// arbitraries
const arbLabels = fc
  .uniqueArray(fc.nat(31), { maxLength: 6 })
  .map((xs) => [...xs].sort((a, b) => a - b));
const arbRow: fc.Arbitrary<Row> = fc.record({
  labels: arbLabels,
  tail: fc.option(fc.nat(4), { nil: null }),
});
const FRESH = 999; // any var disjoint from the small generated space

describe("semilattice laws (mirror of the F* theorems)", () => {
  it("union is commutative, idempotent, associative, with empty identity", () => {
    fc.assert(
      fc.property(arbLabels, arbLabels, arbLabels, (a, b, c) => {
        expect(union(a, b)).toEqual(union(b, a));
        expect(union(a, a)).toEqual(canon(a));
        expect(union(a, union(b, c))).toEqual(union(union(a, b), c));
        expect(union(a, [])).toEqual(canon(a));
      }),
    );
  });

  it("canon is idempotent and order-insensitive", () => {
    fc.assert(
      fc.property(fc.array(fc.nat(31)), (xs) => {
        const c = canon(xs);
        expect(canon(c)).toEqual(c);
        expect(canon([...xs].reverse())).toEqual(c);
      }),
    );
  });
});

describe("differential: transpiler.unify vs verified oracle", () => {
  let oracle: Oracle;
  beforeAll(() => { oracle = new Oracle(ORACLE_EXE); });
  afterAll(() => { oracle?.close(); });

  const oracleSubst = async (r1: Row, r2: Row): Promise<Subst | null> => {
    const r = await oracle.unify(FRESH, r1, r2);
    return r.ok ? (r.subst as Subst) : null;
  };

  it("agrees on 2000 random row pairs (by denotation)", async () => {
    await fc.assert(
      fc.asyncProperty(arbRow, arbRow, async (r1, r2) => {
        const mine = unify.unify(FRESH, r1, r2);
        const truth = await oracleSubst(r1, r2);
        return sameResult(r1, r2, mine, truth);
      }),
      { numRuns: 2000 },
    );
  });

  // frozen regressions: every shrunk counterexample you ever find goes here.
  it.each(GOLDEN as { r1: Row; r2: Row }[])(
    "golden case %#",
    async ({ r1, r2 }) => {
      const mine = unify.unify(FRESH, r1, r2);
      const truth = await oracleSubst(r1, r2);
      expect(sameResult(r1, r2, mine, truth)).toBe(true);
    },
  );
});

// pure sanity on the comparison primitive itself
describe("denotation comparison", () => {
  it("treats fresh-var renaming as equal", () => {
    const r1: Row = { labels: [1], tail: 0 };
    const r2: Row = { labels: [2], tail: 1 };
    const a: Subst = [[0, { labels: [2], tail: 7 }], [1, { labels: [1], tail: 7 }]];
    const b: Subst = [[0, { labels: [2], tail: 8 }], [1, { labels: [1], tail: 8 }]];
    expect(sameResult(r1, r2, a, b)).toBe(true);
  });
});
