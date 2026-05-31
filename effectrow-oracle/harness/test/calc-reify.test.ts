// calc-reify.test.ts -- the reification machine (execreify) vs an INDEPENDENT
// TS CPS interpreter.
//
// `Bang/CalcReify.lean` (ADR-0015) is the K3 frontier: first-class, multi-shot,
// non-tail resumptions. It is the one machine with no in-Lean reference `eval` --
// a reference would itself be a second abstract machine (the bisimulation is the
// open theorem). So the cross-check here is empirical and *independent*: the Lean
// machine reifies the continuation into `Kont`/`Frame` data and splices it by hand
// (forced by strict positivity); the TS oracle (`reify-cps.ts`) is a direct
// free-monad CPS interpreter where a resumption is a real JS closure -- no
// positivity constraint, a genuinely different implementation of the same
// semantics. Agreement on thousands of random multi-shot / non-tail programs is
// strong evidence the hand-built splicing is correct.

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import * as fc from "fast-check";
import { Oracle, type ReifyOut } from "../src/oracle-client.js";
import { runReify, type E, type RVal } from "../src/reify-cps.js";

const ORACLE_EXE = process.env.ORACLE_EXE ?? "../oracle-lean/.lake/build/bin/oracle";
const FUEL = 2_000_000;

// CalcReify.Src builders (de Bruijn indices), matching the oracle wire format.
const val = (n: number): E => ({ t: "val", n });
const vr = (i: number): E => ({ t: "var", i });
const add = (a: E, b: E): E => ({ t: "add", a, b });
const letE = (e1: E, e2: E): E => ({ t: "let", e1, e2 });
const perform = (arg: E): E => ({ t: "perform", arg });
const handle = (clause: E, body: E): E => ({ t: "handle", clause, body });
const resume = (k: E, v: E): E => ({ t: "resume", k, v });

const int = (n: number): RVal => ({ v: "int", n });

// Agree if both are notok, or both ok with the same value (cont is opaque).
function agree(a: ReifyOut, b: { ok: true; value: RVal } | { ok: false }): boolean {
  if (a.ok !== b.ok) return false;
  if (!a.ok || !b.ok) return true; // both notok
  if (a.value.v !== b.value.v) return false;
  if (a.value.v === "int" && b.value.v === "int") return a.value.n === b.value.n;
  return true; // both cont
}

// body `add (perform 5) 1000`: the captured continuation is "λr. r + 1000".
const bodyP: E = add(perform(val(5)), val(1000));

describe("reification machine (execreify) vs independent TS CPS interpreter", () => {
  let oracle: Oracle;
  beforeAll(() => { oracle = new Oracle(ORACLE_EXE); });
  afterAll(() => { oracle?.close(); });

  // The seven CalcReify demonstrators (the `rfl`-proven examples in the Lean file),
  // plus a few extra shapes. Both the machine and the TS oracle must hit `want`.
  it.each([
    { name: "one-shot, NON-TAIL (resume then +100)",
      p: handle(add(resume(vr(1), val(7)), val(100)), bodyP), want: int(1107) },
    { name: "one-shot, tail",
      p: handle(resume(vr(1), val(7)), bodyP), want: int(1007) },
    { name: "MULTI-SHOT (resume twice)",
      p: handle(add(resume(vr(1), val(7)), resume(vr(1), val(20))), bodyP), want: int(2027) },
    { name: "ZERO-shot (continuation discarded)",
      p: handle(val(999), bodyP), want: int(999) },
    { name: "normal return passes through the handler",
      p: handle(vr(0), val(42)), want: int(42) },
    { name: "re-handling (perform inside a resumption)",
      p: handle(resume(vr(1), val(7)), add(perform(val(1)), perform(val(2)))), want: int(14) },
    { name: "payload reaches the clause",
      p: letE(val(5), handle(add(vr(0), resume(vr(1), val(3))), perform(vr(0)))), want: int(8) },

    // extra shapes
    { name: "pure arithmetic, no handler",
      p: add(val(2), add(val(3), val(4))), want: int(9) },
    { name: "triple multi-shot (resume three times)",
      p: handle(add(resume(vr(1), val(1)), add(resume(vr(1), val(2)), resume(vr(1), val(3)))), bodyP),
      want: int(3006) },
    { name: "handler-install env reaches the clause at index 2 (payload@0, resume@1)",
      p: letE(val(10), handle(add(vr(2), resume(vr(1), val(5))), perform(val(0)))), want: int(15) },
  ])("golden: execreify === TS CPS === want -- $name", async ({ p, want }) => {
    const ts = runReify(p);
    expect(ts).toMatchObject({ ok: true, value: want });
    const machine = await oracle.execReify(FUEL, p);
    expect(agree(machine, ts)).toBe(true);
  });

  // notok shapes: both sides report notok (stuck on both, conflated with OOM).
  it.each([
    { name: "unhandled top-level perform", p: perform(val(5)) },
    { name: "resume a non-continuation", p: resume(val(3), val(4)) },
    { name: "unbound variable", p: vr(7) },
    { name: "direct perform in a clause is unhandled (single-depth)",
      p: handle(perform(val(1)), bodyP) },
    { name: "type error: add a continuation",
      p: handle(add(vr(1), val(1)), bodyP) },
  ])("golden notok: execreify === TS CPS === notok -- $name", async ({ p }) => {
    const ts = runReify(p);
    expect(ts.ok).toBe(false);
    const machine = await oracle.execReify(FUEL, p);
    expect(machine.ok).toBe(false);
    expect(agree(machine, ts)).toBe(true);
  });

  // Random closed programs over the full reification fragment. The generator
  // tracks which de Bruijn indices are bound to resumptions (so `resume` targets a
  // real continuation often enough to exercise multi-shot / non-tail / deep paths);
  // ill-formed picks just land on notok===notok, which is also a valid check.
  function arbReify(): fc.Arbitrary<E> {
    // `vars` = total bindings in scope; `konts` = indices currently bound to a
    // resumption. A `let` shifts both by +1; entering a clause adds index 1 (the
    // resumption) and shifts the captured konts by +2 (payload@0, resume@1).
    const go = (depth: number, vars: number, konts: number[]): fc.Arbitrary<E> => {
      const leaf: fc.Arbitrary<E> = vars === 0
        ? fc.integer({ min: -9, max: 9 }).map(val)
        : fc.oneof(fc.integer({ min: -9, max: 9 }).map(val), fc.nat(vars - 1).map(vr));
      if (depth <= 0) return leaf;
      const sub = () => go(depth - 1, vars, konts);
      const subLet = () => go(depth - 1, vars + 1, konts.map((k) => k + 1));
      const clauseVars = vars + 2;
      const clauseKonts = [1, ...konts.map((k) => k + 2)];
      const subClause = () => go(depth - 1, clauseVars, clauseKonts);
      const arms: fc.WeightedArbitrary<E>[] = [
        { weight: 3, arbitrary: leaf },
        { weight: 3, arbitrary: fc.tuple(sub(), sub()).map(([a, b]) => add(a, b)) },
        { weight: 2, arbitrary: fc.tuple(sub(), subLet()).map(([e1, e2]) => letE(e1, e2)) },
        { weight: 2, arbitrary: sub().map(perform) },
        { weight: 3, arbitrary: fc.tuple(subClause(), sub()).map(([clause, body]) => handle(clause, body)) },
      ];
      if (konts.length > 0) {
        // bias resume to target a real resumption index -> genuine multi-shot/non-tail
        arms.push({
          weight: 3,
          arbitrary: fc.tuple(fc.constantFrom(...konts), sub()).map(([k, v]) => resume(vr(k), v)),
        });
      }
      return fc.oneof(...arms);
    };
    return go(4, 0, []);
  }

  it("agrees with the TS CPS interpreter on 2000 random programs", async () => {
    await fc.assert(
      fc.asyncProperty(arbReify(), async (p) => {
        const ts = runReify(p);
        const machine = await oracle.execReify(FUEL, p);
        return agree(machine, ts);
      }),
      { numRuns: 2000 },
    );
  });
});
