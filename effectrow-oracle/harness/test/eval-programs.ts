// eval-programs.ts -- the golden core programs for the `eval` oracle.
//
// Each entry is a closed BANG core program plus the value it MUST evaluate to.
// The differential test asserts: candidate(prog) === oracle(prog) === expected,
// so a golden pins down behavior in BOTH the reference and the candidate. New
// shrunk counterexamples from the fuzzer get frozen here.

import {
  type Expr, type RunResult,
  lit, unit, v, lam, app, thunk, force, letE, con, matchE, ifE, binop,
  handle, stateH, throwsH, seq, get, put, raise,
  pvar, pcon,
} from "../src/ast.js";

export interface Golden { name: string; prog: Expr; expect: RunResult; note: string }

const S = 0; // State effect label
const T = 1; // Throws effect label

// increment State[S] once: put(get + 1)
const inc = put(S, binop("+", get(S), lit(1)));

export const GOLDENS: Golden[] = [
  {
    name: "thunk/force",
    note: "a description forced to a value -- $((20+22)) = 42",
    prog: force(thunk(binop("+", lit(20), lit(22)))),
    expect: { ok: true, value: { v: "int", n: 42 } },
  },
  {
    name: "lambda + application (CBN arg)",
    note: "(\\x. x + 1) 41 -- arg passed as a description, forced by +",
    prog: app(lam("x", binop("+", v("x"), lit(1))), lit(41)),
    expect: { ok: true, value: { v: "int", n: 42 } },
  },
  {
    name: "let is immutable + lexical shadowing",
    note: "let x=1 in let x=2 in $x = 2",
    prog: letE("x", lit(1), letE("x", lit(2), force(v("x")))),
    expect: { ok: true, value: { v: "int", n: 2 } },
  },
  {
    name: "if on a comparison",
    note: "if 2 < 5 then 100 else 200 = 100",
    prog: ifE(binop("<", lit(2), lit(5)), lit(100), lit(200)),
    expect: { ok: true, value: { v: "int", n: 100 } },
  },
  {
    name: "ADT + pattern match (lazy args forced in the arm)",
    note: "match Pair(3,4) { Pair(a,b) -> a + b } = 7",
    prog: matchE(con("Pair", [lit(3), lit(4)]), [
      [pcon("Pair", [pvar("a"), pvar("b")]), binop("+", v("a"), v("b"))],
    ]),
    expect: { ok: true, value: { v: "int", n: 7 } },
  },
  {
    name: "State counter (one-shot handler, resume once)",
    note: "handle State(0) { inc; inc; inc; get } = 3",
    prog: handle(stateH(S, lit(0)), seq(inc, seq(inc, seq(inc, get(S))))),
    expect: { ok: true, value: { v: "int", n: 3 } },
  },
  {
    name: "Throws raise (zero-shot handler, discard resumption)",
    note: "handle Throws(1) { raise 99; 0 } = Err(99)  (the `;0` is dead)",
    prog: handle(throwsH(T), seq(raise(T, lit(99)), lit(0))),
    expect: { ok: true, value: { v: "con", c: "Err", args: [{ v: "int", n: 99 }] } },
  },
  {
    name: "Throws normal exit wraps in Ok",
    note: "handle Throws(1) { 7 } = Ok(7)",
    prog: handle(throwsH(T), lit(7)),
    expect: { ok: true, value: { v: "con", c: "Ok", args: [{ v: "int", n: 7 } ] } },
  },
  {
    name: "effect forwarding across handlers",
    note: "State(0) outside, Throws(1) inside; `get` forwards out past Throws to State. " +
          "put 5; (handle Throws { raise (get); 0 }) -> Err(5)",
    prog: handle(stateH(S, lit(0)),
      seq(put(S, lit(5)),
        handle(throwsH(T), seq(raise(T, get(S)), lit(0))))),
    expect: { ok: true, value: { v: "con", c: "Err", args: [{ v: "int", n: 5 }] } },
  },
  {
    name: "uncaught effect is loud (no handler installed)",
    note: "perform State.get with no handler -> uncaught, not a value",
    prog: get(S),
    expect: { ok: false, reason: "uncaught", label: S, effOp: "get" },
  },
];
