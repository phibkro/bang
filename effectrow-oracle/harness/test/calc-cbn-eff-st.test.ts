// calc-cbn-eff-st.test.ts -- the combined CBN + Throws + State machine vs `eval`.
//
// The K3 capstone (`Bang/CalcCBNEffSt.lean`, ADR-0014): both effects in ONE machine
// (handler stack + state register) over the closure/CBN core -- the effect-row model
// realised. The interesting content is the *interaction*: State PERSISTS through a
// throw (the register threads through unwinding), so a `put` before a `throw` is
// kept, a handler catching it resumes from the throw-time state, and an uncaught
// throw carries the state to the top. eval and machine must agree on (outcome,
// value/payload, finalState) for every program.

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fc from "fast-check";
import { Oracle, type CbnEffStOut, type EffVal } from "../src/oracle-client.js";

const ORACLE_EXE = process.env.ORACLE_EXE ?? "../oracle-lean/.lake/build/bin/oracle";
const FUEL = 100_000;

// CalcCBNEffSt.Src builders (de Bruijn indices).
type E = object;
const val = (n: number): E => ({ t: "val", n });
const vr = (i: number): E => ({ t: "var", i });
const add = (a: E, b: E): E => ({ t: "add", a, b });
const lam = (body: E): E => ({ t: "lam", body });
const app = (f: E, a: E): E => ({ t: "app", f, a });
const letE = (e1: E, e2: E): E => ({ t: "let", e1, e2 });
const thunk = (e: E): E => ({ t: "thunk", e });
const force = (e: E): E => ({ t: "force", e });
const get: E = { t: "get" };
const put = (arg: E): E => ({ t: "put", arg });
const perform = (l: number, arg: E): E => ({ t: "perform", l, arg });
const handle = (l: number, onRaise: E, body: E): E => ({ t: "handle", l, onRaise, body });

const int = (n: number): EffVal => ({ v: "int", n });

function valEq(x: EffVal, y: EffVal): boolean {
  if (x.v !== y.v) return false;
  if (x.v === "int" && y.v === "int") return x.n === y.n;
  return true;
}

// eval and machine must agree exactly: outcome, value/payload, final state, failure.
function agree(a: CbnEffStOut, b: CbnEffStOut): boolean {
  if (a.ok !== b.ok) return false;
  if (!a.ok && !b.ok) return a.reason === b.reason;
  if (a.ok && b.ok) {
    if (a.outcome !== b.outcome) return false;
    if (a.outcome === "ret" && b.outcome === "ret") return valEq(a.value, b.value) && a.state === b.state;
    if (a.outcome === "exc" && b.outcome === "exc")
      return a.label === b.label && valEq(a.payload, b.payload) && a.state === b.state;
  }
  return false;
}

describe("combined CBN + Throws + State machine (execcbneffst) vs reference eval", () => {
  let oracle: Oracle;
  beforeAll(() => { oracle = new Oracle(ORACLE_EXE); });
  afterAll(() => { oracle?.close(); });

  it.each([
    // -- each effect still works alone --
    { name: "pure state: put then get", p: add(put(val(3)), get), want: { outcome: "ret", value: int(3), state: 3 } },
    { name: "pure throws: handler returns the payload", p: handle(0, vr(0), perform(0, val(9))),
      want: { outcome: "ret", value: int(9), state: 0 } },

    // -- the interaction: STATE PERSISTS THROUGH A THROW --
    { name: "a caught throw resumes from the throw-time state",
      p: handle(0, get, add(put(val(5)), perform(0, val(0)))), want: { outcome: "ret", value: int(5), state: 5 } },
    { name: "an uncaught throw carries the state to the top",
      p: add(put(val(7)), perform(0, val(0))), want: { outcome: "exc", label: 0, payload: int(0), state: 7 } },
    { name: "the recovery sees both the payload and the carried state",
      p: handle(0, add(vr(0), get), add(put(val(4)), perform(0, val(100)))),
      want: { outcome: "ret", value: int(104), state: 4 } },

    // -- state carried through the re-throw at a function-call boundary --
    { name: "a put+throw inside a called function: state carried to the outer handler",
      p: handle(0, get, app(lam(add(put(val(8)), perform(0, val(0)))), val(0))),
      want: { outcome: "ret", value: int(8), state: 8 } },

    // -- state carried through label forwarding --
    { name: "a forwarded throw carries the state to the outer handler",
      p: handle(1, get, handle(0, vr(0), add(put(val(6)), perform(1, val(0))))),
      want: { outcome: "ret", value: int(6), state: 6 } },

    // -- laziness still suppresses an unforced effect --
    { name: "an unforced thunk's put never runs (laziness)",
      p: letE(thunk(put(val(1))), get), want: { outcome: "ret", value: int(0), state: 0 } },
  ])("golden: execcbneffst === evalcbneffst === expected -- $name", async ({ p, want }) => {
    const machine = await oracle.execCbnEffSt(FUEL, p);
    const reference = await oracle.evalCbnEffSt(FUEL, p);
    expect(reference).toMatchObject(want as object);
    expect(agree(machine, reference)).toBe(true);
  });

  // random closed programs over the full combined fragment
  function arbCbnEffSt(): fc.Arbitrary<E> {
    const go = (depth: number, vars: number, labels: number[]): fc.Arbitrary<E> => {
      const leaf: fc.Arbitrary<E> = vars === 0
        ? fc.oneof(fc.integer({ min: -9, max: 9 }).map(val), fc.constant(get))
        : fc.oneof(fc.integer({ min: -9, max: 9 }).map(val), fc.constant(get), fc.nat(vars - 1).map(vr));
      if (depth <= 0) return leaf;
      const sub = () => go(depth - 1, vars, labels);
      const subV = () => go(depth - 1, vars + 1, labels);
      return fc.oneof(
        { weight: 2, arbitrary: leaf },
        { weight: 2, arbitrary: fc.tuple(sub(), sub()).map(([a, b]) => add(a, b)) },
        { weight: 1, arbitrary: subV().map(lam) },
        { weight: 2, arbitrary: fc.tuple(sub(), sub()).map(([f, a]) => app(f, a)) },
        { weight: 1, arbitrary: fc.tuple(sub(), subV()).map(([e1, e2]) => letE(e1, e2)) },
        { weight: 1, arbitrary: sub().map(thunk) },
        { weight: 1, arbitrary: sub().map(force) },
        { weight: 1, arbitrary: sub().map(put) },
        { weight: 1, arbitrary: fc.tuple(fc.constantFrom(...labels), sub()).map(([l, a]) => perform(l, a)) },
        { weight: 1, arbitrary: fc.tuple(fc.constantFrom(...labels), subV(), sub())
            .map(([l, onR, body]) => handle(l, onR, body)) },
      );
    };
    return go(4, 0, [0, 1, 2]);
  }

  it("agrees with eval on 500 random combined programs", async () => {
    await fc.assert(
      fc.asyncProperty(arbCbnEffSt(), async (p) => {
        const machine = await oracle.execCbnEffSt(FUEL, p);
        const reference = await oracle.evalCbnEffSt(FUEL, p);
        return agree(machine, reference);
      }),
      { numRuns: 500 },
    );
  });
});
