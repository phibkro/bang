// calc-cbn-eff.test.ts -- the composed CBN+Throws machine vs its reference `eval`.
//
// The real K3 composition (`Bang/CalcCBNEff.lean`, ADR-0012): zero-shot Throws
// fused into the call-by-name closure/thunk core. The interesting, genuinely new
// behaviour is that **forcing can raise** and that an effect can **escape a
// function call / a thunk-force** -- the machine re-throws an escaping `uncaught`
// at the meta-call boundary against the outer handler stack. The reference `eval`
// (fuel-bounded `Option Outcome`) and the machine (`Option Result`) must agree on
// every program, value-for-value (both force the top result to WHNF).

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fc from "fast-check";
import { Oracle, type CbnEffOutcome, type EffVal } from "../src/oracle-client.js";

const ORACLE_EXE = process.env.ORACLE_EXE ?? "../oracle-lean/.lake/build/bin/oracle";
const FUEL = 100_000;

// CalcCBNEff.Src builders (de Bruijn indices).
type E = object;
const val = (n: number): E => ({ t: "val", n });
const vr = (i: number): E => ({ t: "var", i });
const add = (a: E, b: E): E => ({ t: "add", a, b });
const lam = (body: E): E => ({ t: "lam", body });
const app = (f: E, a: E): E => ({ t: "app", f, a });
const letE = (e1: E, e2: E): E => ({ t: "let", e1, e2 });
const thunk = (e: E): E => ({ t: "thunk", e });
const force = (e: E): E => ({ t: "force", e });
const perform = (l: number, arg: E): E => ({ t: "perform", l, arg });
const handle = (l: number, onRaise: E, body: E): E => ({ t: "handle", l, onRaise, body });

const int = (n: number): EffVal => ({ v: "int", n });

function valEq(x: EffVal, y: EffVal): boolean {
  if (x.v !== y.v) return false;
  if (x.v === "int" && y.v === "int") return x.n === y.n;
  return true; // clos / thunk are opaque, equal by tag
}

// eval and machine must agree exactly: same value, same effect, same failure.
function agree(a: CbnEffOutcome, b: CbnEffOutcome): boolean {
  if (a.ok !== b.ok) return false;
  if (!a.ok && !b.ok) return a.reason === b.reason;
  if (a.ok && b.ok) {
    if (a.outcome !== b.outcome) return false;
    if (a.outcome === "ret" && b.outcome === "ret") return valEq(a.value, b.value);
    if (a.outcome === "exc" && b.outcome === "exc") return a.label === b.label && valEq(a.payload, b.payload);
  }
  return false;
}

describe("composed CBN+Throws machine (execcbneff) vs reference eval", () => {
  let oracle: Oracle;
  beforeAll(() => { oracle = new Oracle(ORACLE_EXE); });
  afterAll(() => { oracle?.close(); });

  it.each([
    // -- pure CBN core still works through the composed machine --
    { name: "force a thunk passed to a function", p: app(lam(force(vr(0))), val(5)),
      want: { outcome: "ret", value: int(5) } },
    { name: "add through forcing", p: add(val(2), val(3)),
      want: { outcome: "ret", value: int(5) } },

    // -- effects escape a function call: re-throw at the APP boundary --
    { name: "uncaught effect escapes a function call", p: app(lam(perform(0, val(7))), val(0)),
      want: { outcome: "exc", label: 0, payload: int(7) } },
    { name: "handler catches an effect raised INSIDE a called function",
      p: handle(0, vr(0), app(lam(perform(0, val(9))), val(0))),
      want: { outcome: "ret", value: int(9) } },
    { name: "captured closure raises; outer handler recovers with payload",
      p: handle(0, add(vr(0), val(1)), letE(lam(perform(0, val(11))), app(vr(0), val(0)))),
      want: { outcome: "ret", value: int(12) } },

    // -- forcing can raise: re-throw at the FORCE boundary --
    { name: "forcing a thunk raises; handler recovers (5+100)",
      p: handle(0, add(vr(0), val(100)), force(thunk(perform(0, val(5))))),
      want: { outcome: "ret", value: int(105) } },
    { name: "nested thunk-forces propagate the effect",
      p: force(thunk(force(thunk(perform(0, val(8)))))),
      want: { outcome: "exc", label: 0, payload: int(8) } },

    // -- laziness suppresses an effect: an unforced thunk never performs --
    { name: "unforced thunk's effect never happens (laziness)",
      p: letE(thunk(perform(0, val(1))), val(42)),
      want: { outcome: "ret", value: int(42) } },

    // -- short-circuit + label forwarding across a call boundary --
    { name: "add short-circuits on a raise (forced operand)", p: add(val(1), perform(0, val(9))),
      want: { outcome: "exc", label: 0, payload: int(9) } },
    { name: "wrong label forwards out of a call to the outer handler",
      p: handle(1, vr(0), app(lam(handle(0, vr(0), perform(1, val(3)))), val(0))),
      want: { outcome: "ret", value: int(3) } },
  ])("golden: execcbneff === evalcbneff === expected -- $name", async ({ p, want }) => {
    const machine = await oracle.execCbnEff(FUEL, p);
    const reference = await oracle.evalCbnEff(FUEL, p);
    expect(reference).toMatchObject(want as object);
    expect(agree(machine, reference)).toBe(true);
  });

  // random closed programs over the full composed fragment
  function arbCbnEff(): fc.Arbitrary<E> {
    const go = (depth: number, vars: number, labels: number[]): fc.Arbitrary<E> => {
      const leaf: fc.Arbitrary<E> = vars === 0
        ? fc.integer({ min: -9, max: 9 }).map(val)
        : fc.oneof(fc.integer({ min: -9, max: 9 }).map(val), fc.nat(vars - 1).map(vr));
      if (depth <= 0) return leaf;
      const sub = () => go(depth - 1, vars, labels);
      const subV = () => go(depth - 1, vars + 1, labels); // one more binding in scope
      return fc.oneof(
        { weight: 2, arbitrary: leaf },
        { weight: 2, arbitrary: fc.tuple(sub(), sub()).map(([a, b]) => add(a, b)) },
        { weight: 1, arbitrary: subV().map(lam) },
        { weight: 2, arbitrary: fc.tuple(sub(), sub()).map(([f, a]) => app(f, a)) },
        { weight: 1, arbitrary: fc.tuple(sub(), subV()).map(([e1, e2]) => letE(e1, e2)) },
        { weight: 1, arbitrary: sub().map(thunk) },
        { weight: 1, arbitrary: sub().map(force) },
        { weight: 1, arbitrary: fc.tuple(fc.constantFrom(...labels), sub()).map(([l, a]) => perform(l, a)) },
        { weight: 1, arbitrary: fc.tuple(fc.constantFrom(...labels), subV(), sub())
            .map(([l, onR, body]) => handle(l, onR, body)) },
      );
    };
    return go(4, 0, [0, 1, 2]);
  }

  it("agrees with eval on 500 random composed programs", async () => {
    await fc.assert(
      fc.asyncProperty(arbCbnEff(), async (p) => {
        const machine = await oracle.execCbnEff(FUEL, p);
        const reference = await oracle.evalCbnEff(FUEL, p);
        return agree(machine, reference);
      }),
      { numRuns: 500 },
    );
  });
});
