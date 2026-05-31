// eval-candidate.ts -- THE CODE UNDER TEST (a candidate `eval`).
//
// An intentionally INDEPENDENT re-derivation of the BANG core semantics, to be
// driven against the verified Lean `eval` oracle (ADR-0008) by the differential
// harness. Where the reference is a fuel-bounded free-monad interpreter whose
// handlers are a deep fold, this candidate is a direct tree-walker: State is a
// mutable cell on a handler stack, and Throws is a JS exception. Two genuinely
// different strategies that must nonetheless agree on every terminating program
// -- that disagreement is what the harness is built to catch.
//
// Call-by-name (ADR-0008): bindings hold descriptions (thunks); `$` forces to
// WHNF. Effects fire exactly when a `perform` is reached in forcing position.

import type { Expr, RunResult, Value } from "./ast.js";

type Env = { name: string; val: CV }[];
type CV =
  | { tag: "int"; n: number }
  | { tag: "unit" }
  | { tag: "clos"; x: string; body: Expr; env: Env }
  | { tag: "con"; c: string; args: CV[] }
  | { tag: "thunk"; e: Expr; env: Env };

type Frame =
  | { kind: "state"; label: number; cur: CV }
  | { kind: "throws"; label: number };

// control-flow signals (not program values)
class Raise { constructor(public label: number, public value: CV) {} }
class Stuck { constructor(public msg: string) {} }
class OutOfFuel {}

class Interp {
  stack: Frame[] = [];
  fuel: number;
  constructor(fuel: number) { this.fuel = fuel; }

  private tick() { if (--this.fuel <= 0) throw new OutOfFuel(); }

  private lookup(x: string, env: Env): CV {
    for (let i = env.length - 1; i >= 0; i--) if (env[i]!.name === x) return env[i]!.val;
    throw new Stuck(`unbound variable ${x}`);
  }

  // Evaluate an expression to a value (possibly an unforced thunk -- CBN).
  eval(e: Expr, env: Env): CV {
    this.tick();
    switch (e.t) {
      case "lit":   return { tag: "int", n: e.v };
      case "unit":  return { tag: "unit" };
      case "var":   return this.lookup(e.x, env);
      case "lam":   return { tag: "clos", x: e.x, body: e.body, env };
      case "thunk": return { tag: "thunk", e: e.e, env };
      case "force": return this.force(this.eval(e.e, env));
      case "let":   return this.eval(e.e2, [...env, { name: e.x, val: { tag: "thunk", e: e.e1, env } }]);
      case "app": {
        const f = this.force(this.eval(e.f, env));
        if (f.tag !== "clos") throw new Stuck("application of a non-function");
        return this.eval(f.body, [...f.env, { name: f.x, val: { tag: "thunk", e: e.a, env } }]);
      }
      case "con":   return { tag: "con", c: e.c, args: e.args.map((a) => ({ tag: "thunk", e: a, env } as CV)) };
      case "if": {
        const c = this.force(this.eval(e.c, env));
        if (c.tag === "con" && c.c === "True" && c.args.length === 0) return this.eval(e.then, env);
        if (c.tag === "con" && c.c === "False" && c.args.length === 0) return this.eval(e.else, env);
        throw new Stuck("if-condition is not a Bool");
      }
      case "binop": {
        const a = this.force(this.eval(e.a, env));
        const b = this.force(this.eval(e.b, env));
        if (a.tag !== "int" || b.tag !== "int") throw new Stuck("binop on non-integers");
        return this.prim(e.op, a.n, b.n);
      }
      case "match": {
        const s = this.force(this.eval(e.scrut, env));
        for (const arm of e.arms) {
          const bs = matchPat(arm.pat, s);
          if (bs) return this.eval(arm.rhs, [...env, ...bs]);
        }
        throw new Stuck("no pattern matched");
      }
      case "perform": {
        const arg = this.force(this.eval(e.arg, env));
        return this.performOp(e.label, e.op, arg);
      }
      case "handle": return this.handle(e, env);
    }
  }

  // Force a value to weak head normal form, performing effects along the way.
  private force(val: CV): CV {
    let v = val;
    while (v.tag === "thunk") { this.tick(); v = this.eval(v.e, v.env); }
    return v;
  }

  private prim(op: string, a: number, b: number): CV {
    switch (op) {
      case "+": return { tag: "int", n: a + b };
      case "-": return { tag: "int", n: a - b };
      case "*": return { tag: "int", n: a * b };
      case "<": return { tag: "con", c: a < b ? "True" : "False", args: [] };
      case "==": return { tag: "con", c: a === b ? "True" : "False", args: [] };
      default:  throw new Stuck(`bad binop ${op}`);
    }
  }

  // Dispatch an effect to the nearest handler on the stack that owns its label.
  private performOp(label: number, op: string, arg: CV): CV {
    for (let i = this.stack.length - 1; i >= 0; i--) {
      const fr = this.stack[i]!;
      if (fr.kind === "state" && fr.label === label) {
        if (op === "get") return fr.cur;
        if (op === "put") { fr.cur = arg; return { tag: "unit" }; }
        // unknown op for this effect: keep searching outward
      } else if (fr.kind === "throws" && fr.label === label) {
        if (op === "raise") throw new Raise(label, arg);
      }
    }
    // escaped every handler -> surface as an uncaught effect (loud)
    throw new Uncaught(label, op);
  }

  private handle(e: Extract<Expr, { t: "handle" }>, env: Env): CV {
    if (e.h.h === "throws") {
      const label = e.h.label;
      this.stack.push({ kind: "throws", label });
      try {
        const bv = this.eval(e.body, env);
        return { tag: "con", c: "Ok", args: [bv] };           // deep handler: wrap normal result
      } catch (ex) {
        if (ex instanceof Raise && ex.label === label) return { tag: "con", c: "Err", args: [ex.value] };
        throw ex;                                              // forward to an outer handler
      } finally {
        this.stack.pop();
      }
    } else {
      const label = e.h.label;
      const s0 = this.force(this.eval(e.h.init, env));         // init state forced outside the handler
      this.stack.push({ kind: "state", label, cur: s0 });
      try {
        return this.eval(e.body, env);                         // state handler returns the body value as-is
      } finally {
        this.stack.pop();
      }
    }
  }

  // Deep-force a value for display (force thunks, recurse into constructor args).
  deepForce(val: CV): CV {
    const v = this.force(val);
    if (v.tag === "con") return { tag: "con", c: v.c, args: v.args.map((a) => this.deepForce(a)) };
    return v;
  }
}

class Uncaught { constructor(public label: number, public op: string) {} }

function matchPat(p: import("./ast.js").Pat, v: CV): Env | null {
  switch (p.p) {
    case "wild": return [];
    case "var":  return [{ name: p.x, val: v }];
    case "lit":  return v.tag === "int" && v.n === p.v ? [] : null;
    case "con": {
      if (v.tag !== "con" || v.c !== p.c || v.args.length !== p.args.length) return null;
      const out: Env = [];
      for (let i = 0; i < p.args.length; i++) {
        const bs = matchPat(p.args[i]!, v.args[i]!);   // nested: arg is a still-lazy thunk -> only var/wild bind
        if (!bs) return null;
        out.push(...bs);
      }
      return out;
    }
  }
}

function toWire(v: CV): Value {
  switch (v.tag) {
    case "int":   return { v: "int", n: v.n };
    case "unit":  return { v: "unit" };
    case "clos":  return { v: "clos" };
    case "thunk": return { v: "thunk" };
    case "con":   return { v: "con", c: v.c, args: v.args.map(toWire) };
  }
}

/** Run a closed program, mirroring the Lean `run` (eval, then deep-force). */
export function evalCandidate(fuel: number, e: Expr): RunResult {
  const it = new Interp(fuel);
  try {
    const v = it.deepForce(it.eval(e, []));
    return { ok: true, value: toWire(v) };
  } catch (ex) {
    if (ex instanceof OutOfFuel) return { ok: false, reason: "outOfFuel" };
    if (ex instanceof Stuck)     return { ok: false, reason: "stuck", msg: ex.msg };
    if (ex instanceof Uncaught)  return { ok: false, reason: "uncaught", label: ex.label, effOp: ex.op };
    if (ex instanceof Raise)     return { ok: false, reason: "uncaught", label: ex.label, effOp: "raise" };
    throw ex;
  }
}
