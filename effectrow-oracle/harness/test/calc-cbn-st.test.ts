// calc-cbn-st.test.ts -- the composed CBN+State machine vs its reference `eval`.
//
// The second K3 composition (`Bang/CalcCBNSt.lean`, ADR-0013): State
// (get/put/runState) threaded through the call-by-name closure/thunk core. The
// interesting content is that the state register threads through a function call
// and through forcing a thunk (State *resumes*, so -- unlike zero-shot Throws --
// it threads cleanly through the nested meta-runs, no re-throw), that an unforced
// thunk's effect never happens (laziness), and that `runState` localises the cell.
// Reference `eval` and machine must agree on (value, finalState) for every program.

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fc from "fast-check";
import { Oracle, type CbnStOut, type EffVal } from "../src/oracle-client.js";

const ORACLE_EXE = process.env.ORACLE_EXE ?? "../oracle-lean/.lake/build/bin/oracle";
const FUEL = 100_000;

// CalcCBNSt.Src builders (de Bruijn indices).
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
const runState = (init: E, body: E): E => ({ t: "runState", init, body });

const int = (n: number): EffVal => ({ v: "int", n });

function valEq(x: EffVal, y: EffVal): boolean {
  if (x.v !== y.v) return false;
  if (x.v === "int" && y.v === "int") return x.n === y.n;
  return true; // clos / thunk are opaque, equal by tag
}

// eval and machine must agree exactly: same value, same final state, same failure.
function agree(a: CbnStOut, b: CbnStOut): boolean {
  if (a.ok !== b.ok) return false;
  if (!a.ok && !b.ok) return a.reason === b.reason;
  if (a.ok && b.ok) return valEq(a.value, b.value) && a.state === b.state;
  return false;
}

describe("composed CBN+State machine (execcbnst) vs reference eval", () => {
  let oracle: Oracle;
  beforeAll(() => { oracle = new Oracle(ORACLE_EXE); });
  afterAll(() => { oracle?.close(); });

  it.each([
    // -- pure core still works; initial state is 0 --
    { name: "pure add", p: add(val(1), val(2)), want: { value: int(3), state: 0 } },
    { name: "get reads the initial state", p: get, want: { value: int(0), state: 0 } },
    { name: "put forces its arg, sets the state, returns 0", p: put(val(5)), want: { value: int(0), state: 5 } },

    // -- state threads left-to-right through a binop --
    { name: "put then get (5+threaded)", p: add(put(val(5)), get), want: { value: int(5), state: 5 } },

    // -- state threads through a FUNCTION CALL (the composition payoff) --
    { name: "a put inside a called function persists",
      p: add(app(lam(put(vr(0))), val(7)), get), want: { value: int(7), state: 7 } },
    { name: "a captured closure threads state when called",
      p: letE(lam(put(vr(0))), add(app(vr(0), val(3)), get)), want: { value: int(3), state: 3 } },

    // -- state threads through FORCING a thunk --
    { name: "forcing a thunk runs its put",
      p: add(force(thunk(put(val(9)))), get), want: { value: int(9), state: 9 } },

    // -- laziness: an unforced thunk's effect never happens --
    { name: "unforced thunk's put never runs (laziness)",
      p: letE(thunk(put(val(1))), get), want: { value: int(0), state: 0 } },

    // -- runState localises the cell --
    { name: "get inside runState reads the local state", p: runState(val(10), get), want: { value: int(10), state: 0 } },
    { name: "runState's inner put does not leak to the outer state",
      p: add(runState(val(5), put(val(9))), get), want: { value: int(0), state: 0 } },
  ])("golden: execcbnst === evalcbnst === expected -- $name", async ({ p, want }) => {
    const machine = await oracle.execCbnSt(FUEL, p);
    const reference = await oracle.evalCbnSt(FUEL, p);
    expect(reference).toMatchObject(want as object);
    expect(agree(machine, reference)).toBe(true);
  });

  // random closed programs over the full composed fragment
  function arbCbnSt(): fc.Arbitrary<E> {
    const go = (depth: number, vars: number): fc.Arbitrary<E> => {
      const leaf: fc.Arbitrary<E> = vars === 0
        ? fc.oneof(fc.integer({ min: -9, max: 9 }).map(val), fc.constant(get))
        : fc.oneof(fc.integer({ min: -9, max: 9 }).map(val), fc.constant(get), fc.nat(vars - 1).map(vr));
      if (depth <= 0) return leaf;
      const sub = () => go(depth - 1, vars);
      const subV = () => go(depth - 1, vars + 1);
      return fc.oneof(
        { weight: 2, arbitrary: leaf },
        { weight: 2, arbitrary: fc.tuple(sub(), sub()).map(([a, b]) => add(a, b)) },
        { weight: 1, arbitrary: subV().map(lam) },
        { weight: 2, arbitrary: fc.tuple(sub(), sub()).map(([f, a]) => app(f, a)) },
        { weight: 1, arbitrary: fc.tuple(sub(), subV()).map(([e1, e2]) => letE(e1, e2)) },
        { weight: 1, arbitrary: sub().map(thunk) },
        { weight: 1, arbitrary: sub().map(force) },
        { weight: 1, arbitrary: sub().map(put) },
        { weight: 1, arbitrary: fc.tuple(sub(), sub()).map(([i, b]) => runState(i, b)) },
      );
    };
    return go(4, 0);
  }

  it("agrees with eval on 500 random composed programs", async () => {
    await fc.assert(
      fc.asyncProperty(arbCbnSt(), async (p) => {
        const machine = await oracle.execCbnSt(FUEL, p);
        const reference = await oracle.evalCbnSt(FUEL, p);
        return agree(machine, reference);
      }),
      { numRuns: 500 },
    );
  });
});
