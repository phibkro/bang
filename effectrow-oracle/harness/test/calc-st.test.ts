// calc-st.test.ts -- the calculated STATE machine vs its reference `eval`.
//
// K3, State: `Bang/CalcSt.lean` calculates a state-register machine (GET/PUT/
// ENTER/LEAVE) -- get/put resume the computation in tail position, so the state
// threads through the machine, no continuation reification. Both `eval` (total)
// and the machine return { value, state }; they must agree on every program.

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fc from "fast-check";
import { Oracle, type StOut } from "../src/oracle-client.js";

const ORACLE_EXE = process.env.ORACLE_EXE ?? "../oracle-lean/.lake/build/bin/oracle";

// CalcSt.Src builders (de Bruijn indices).
type E = object;
const val = (n: number): E => ({ t: "val", n });
const vr = (i: number): E => ({ t: "var", i });
const add = (a: E, b: E): E => ({ t: "add", a, b });
const letE = (e1: E, e2: E): E => ({ t: "let", e1, e2 });
const get: E = { t: "get" };
const put = (arg: E): E => ({ t: "put", arg });
const runState = (init: E, body: E): E => ({ t: "runState", init, body });

function agree(a: StOut, b: StOut): boolean {
  if (!a.ok || !b.ok) return false;
  return a.value === b.value && a.state === b.state;
}

describe("calculated State machine (execst) vs reference eval", () => {
  let oracle: Oracle;
  beforeAll(() => { oracle = new Oracle(ORACLE_EXE); });
  afterAll(() => { oracle?.close(); });

  it.each([
    { name: "get reads the initial cell", p: runState(val(10), get), want: { value: 10, state: 0 } },
    { name: "get + get in the cell", p: runState(val(10), add(get, get)), want: { value: 20, state: 0 } },
    { name: "put then get", p: runState(val(0), letE(put(val(99)), get)), want: { value: 99, state: 0 } },
    { name: "put returns 0 (unit)", p: runState(val(5), put(val(7))), want: { value: 0, state: 0 } },
    { name: "increment: put(get+1); get", p: runState(val(41), letE(put(add(get, val(1))), get)), want: { value: 42, state: 0 } },
    { name: "runState restores the outer cell",
      // outer cell starts 0; inner runState uses its own cell; top get reads outer (0)
      p: runState(val(0), add(runState(val(100), get), get)), want: { value: 100, state: 0 } },
    { name: "two puts thread through a let-chain",
      p: runState(val(0), letE(put(val(3)), letE(put(add(get, get)), get))), want: { value: 6, state: 0 } },
  ])("golden: execst === evalst === expected -- $name", async ({ p, want }) => {
    const machine = await oracle.execSt(p);
    const reference = await oracle.evalSt(p);
    expect(reference).toMatchObject(want as object);
    expect(agree(machine, reference)).toBe(true);
  });

  // random closed State programs (de Bruijn; get/put/runState/arith/let)
  function arbSt(): fc.Arbitrary<E> {
    const go = (depth: number, vars: number): fc.Arbitrary<E> => {
      const leaf: fc.Arbitrary<E> = fc.oneof(
        fc.integer({ min: -9, max: 9 }).map(val),
        fc.constant(get),
        ...(vars > 0 ? [fc.nat(vars - 1).map(vr)] : []),
      );
      if (depth <= 0) return leaf;
      const sub = () => go(depth - 1, vars);
      return fc.oneof(
        { weight: 1, arbitrary: leaf },
        { weight: 2, arbitrary: fc.tuple(sub(), sub()).map(([a, b]) => add(a, b)) },
        { weight: 1, arbitrary: sub().map((a) => put(a)) },
        { weight: 1, arbitrary: fc.tuple(sub(), go(depth - 1, vars + 1)).map(([e1, e2]) => letE(e1, e2)) },
        { weight: 1, arbitrary: fc.tuple(sub(), sub()).map(([i, b]) => runState(i, b)) },
      );
    };
    return go(4, 0);
  }

  it("agrees with eval on 500 random State programs", async () => {
    await fc.assert(
      fc.asyncProperty(arbSt(), async (p) => {
        const machine = await oracle.execSt(p);
        const reference = await oracle.evalSt(p);
        return agree(machine, reference);
      }),
      { numRuns: 500 },
    );
  });
});
