// calc-eff.test.ts -- the calculated HANDLER machine vs its reference `eval`.
//
// K3 increment: `Bang/CalcEff.lean` calculates a general algebraic-handler machine
// (label-dispatched MARK/UNMARK/THROW + stack unwinding) with Throws as its first
// (zero-shot) operation. The reference `eval` is total (`evaleff` op); the machine
// is fuel-bounded (`execeff` op). They must agree -- value vs propagating-effect
// (`ret` vs `exc`) -- on every program: catch, forward, nest, recover, uncaught.

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fc from "fast-check";
import { Oracle, type Outcome } from "../src/oracle-client.js";

const ORACLE_EXE = process.env.ORACLE_EXE ?? "../oracle-lean/.lake/build/bin/oracle";
const FUEL = 100_000;

// CalcEff.Src builders (de Bruijn indices).
type E = object;
const val = (n: number): E => ({ t: "val", n });
const vr = (i: number): E => ({ t: "var", i });
const add = (a: E, b: E): E => ({ t: "add", a, b });
const letE = (e1: E, e2: E): E => ({ t: "let", e1, e2 });
const perform = (l: number, arg: E): E => ({ t: "perform", l, arg });
const handle = (l: number, onRaise: E, body: E): E => ({ t: "handle", l, onRaise, body });

// compare two Outcomes by observable content (ignores oom -- shouldn't occur here)
function agree(a: Outcome, b: Outcome): boolean {
  if (!a.ok || !b.ok) return false;
  if (a.outcome !== b.outcome) return false;
  if (a.outcome === "ret" && b.outcome === "ret") return a.n === b.n;
  if (a.outcome === "exc" && b.outcome === "exc") return a.label === b.label && a.payload === b.payload;
  return false;
}

describe("calculated handler machine (execeff) vs reference eval -- Throws", () => {
  let oracle: Oracle;
  beforeAll(() => { oracle = new Oracle(ORACLE_EXE); });
  afterAll(() => { oracle?.close(); });

  it.each([
    { name: "uncaught effect propagates", p: perform(0, val(5)), want: { outcome: "exc", label: 0, payload: 5 } },
    { name: "handler catches, recovery returns payload", p: handle(0, vr(0), perform(0, val(7))), want: { outcome: "ret", n: 7 } },
    { name: "normal completion passes through", p: handle(0, vr(0), val(42)), want: { outcome: "ret", n: 42 } },
    { name: "add short-circuits on a raise", p: add(val(1), perform(0, val(9))), want: { outcome: "exc", label: 0, payload: 9 } },
    { name: "recovery uses the payload: 5+100", p: handle(0, add(vr(0), val(100)), perform(0, val(5))), want: { outcome: "ret", n: 105 } },
    { name: "wrong label forwards to outer handler", p: handle(1, val(0), handle(0, vr(0), perform(0, val(3)))), want: { outcome: "ret", n: 3 } },
    { name: "outer handler catches a forwarded effect", p: handle(1, val(77), handle(0, vr(0), perform(1, val(3)))), want: { outcome: "ret", n: 77 } },
    { name: "let binds before a raise, recovery sees the handler's env", p: letE(val(10), handle(0, add(vr(0), vr(1)), perform(0, val(5)))), want: { outcome: "ret", n: 15 } },
  ])("golden: execeff === evaleff === expected -- $name", async ({ p, want }) => {
    const machine = await oracle.execEff(FUEL, p);
    const reference = await oracle.evalEff(p);
    expect(reference).toMatchObject(want as object);
    expect(agree(machine, reference)).toBe(true);
  });

  // random closed effect programs over the de Bruijn fragment
  function arbEff(): fc.Arbitrary<E> {
    const go = (depth: number, vars: number, labels: number[]): fc.Arbitrary<E> => {
      const leaf: fc.Arbitrary<E> = vars === 0
        ? fc.integer({ min: -9, max: 9 }).map(val)
        : fc.oneof(fc.integer({ min: -9, max: 9 }).map(val), fc.nat(vars - 1).map(vr));
      if (depth <= 0) return leaf;
      const sub = () => go(depth - 1, vars, labels);
      return fc.oneof(
        { weight: 1, arbitrary: leaf },
        { weight: 2, arbitrary: fc.tuple(sub(), sub()).map(([a, b]) => add(a, b)) },
        { weight: 1, arbitrary: fc.tuple(sub(), go(depth - 1, vars + 1, labels)).map(([e1, e2]) => letE(e1, e2)) },
        { weight: 1, arbitrary: fc.tuple(fc.constantFrom(...labels), sub()).map(([l, a]) => perform(l, a)) },
        { weight: 1, arbitrary: fc.tuple(fc.constantFrom(...labels), go(depth - 1, vars + 1, labels), sub())
            .map(([l, onR, body]) => handle(l, onR, body)) },
      );
    };
    return go(4, 0, [0, 1, 2]);
  }

  it("agrees with eval on 500 random handler programs", async () => {
    await fc.assert(
      fc.asyncProperty(arbEff(), async (p) => {
        const machine = await oracle.execEff(FUEL, p);
        const reference = await oracle.evalEff(p);
        if (!machine.ok && machine.reason === "outOfFuel") return true;
        return agree(machine, reference);
      }),
      { numRuns: 500 },
    );
  });
});
