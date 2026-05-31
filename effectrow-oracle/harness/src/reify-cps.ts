// reify-cps.ts -- an INDEPENDENT reference for the reification machine.
//
// `Bang/CalcReify.lean` is a *defunctionalized* flat machine: Lean's strict
// positivity forbids a resumption being a meta-function (`vcont : (Value -> ..)`),
// so the continuation is reified into explicit `Kont`/`Frame` data and spliced by
// hand. That is precisely the representation we want to cross-check against an
// implementation that has NO such constraint: this is a direct free-monad CPS
// interpreter of the *same* `Src` language where a resumption is a real JS closure
// `(w) => Comp`. Capture is `op`-node construction; splice is `bind`; the deep
// handler re-installs itself around the resumption. If the two agree on thousands
// of random multi-shot / non-tail programs, the hand-built splicing in the Lean
// machine matches the textbook semantics (ADR-0015's empirical cross-check).
//
// Semantics mirrored from the Lean machine, exactly:
//  * normal return passes THROUGH a handler (the return clause is the identity);
//  * `perform e` is handled by the INNERMOST handler only; the clause binds the
//    payload at de Bruijn index 0 and the resumption at index 1, then the handler-
//    install-time env;
//  * deep handlers: `resume` re-installs the handler around the captured
//    continuation, so a `perform` inside a resumption is re-handled;
//  * single handler depth (ADR-0015 scope): a `perform` reached directly inside a
//    clause (not via a resumption's re-install) is UNHANDLED -> stuck, and is NOT
//    forwarded to an outer handler.

// Source terms -- the same wire shape the oracle's `srcReifyFromJson` decodes.
export type E =
  | { t: "val"; n: number }
  | { t: "var"; i: number }
  | { t: "add"; a: E; b: E }
  | { t: "let"; e1: E; e2: E }
  | { t: "perform"; arg: E }
  | { t: "handle"; clause: E; body: E }
  | { t: "resume"; k: E; v: E };

// Reported WHNF value: an int, or an opaque reified continuation.
export type RVal = { v: "int"; n: number } | { v: "cont" };

// Internal values: a resumption is a real JS closure -- the representation Lean's
// positivity check rejects, which is the whole point of this independent oracle.
type IVal = { tag: "int"; n: number } | { tag: "cont"; resume: (w: IVal) => Comp };

// A computation tree (free monad over the single operation `perform`).
type Comp =
  | { tag: "ret"; v: IVal }
  | { tag: "op"; payload: IVal; k: (w: IVal) => Comp }
  | { tag: "stuck" };

const STUCK: Comp = { tag: "stuck" };
const ret = (v: IVal): Comp => ({ tag: "ret", v });

// Free-monad bind: thread `f` into the continuation of the first `perform`.
function bind(c: Comp, f: (v: IVal) => Comp): Comp {
  if (c.tag === "stuck") return STUCK;
  if (c.tag === "ret") return f(c.v);
  return { tag: "op", payload: c.payload, k: (w) => bind(c.k(w), f) };
}

// Deep handler over a body computation `c`, with the clause's source + the env
// captured where the handler was installed.
function handle(c: Comp, clauseBody: E, clauseEnv: IVal[]): Comp {
  if (c.tag === "stuck") return STUCK;
  if (c.tag === "ret") return c; // identity return: value passes through
  // c is `perform payload, k`: run the clause with (payload@0, resume@1, ..env).
  // The resumption re-installs THIS handler around the captured continuation
  // (deep), so resuming a continuation that performs again re-enters the clause.
  const resumeVal: IVal = { tag: "cont", resume: (w) => handle(c.k(w), clauseBody, clauseEnv) };
  const cr = evalE(clauseBody, [c.payload, resumeVal, ...clauseEnv]);
  // single-handler-depth: a `perform` reached directly in the clause (an op still
  // standing in `cr`, i.e. not consumed by a resumption's re-install) is unhandled.
  return cr.tag === "op" ? STUCK : cr;
}

function evalE(e: E, env: IVal[]): Comp {
  switch (e.t) {
    case "val":
      return ret({ tag: "int", n: e.n });
    case "var": {
      const v = env[e.i];
      return v === undefined ? STUCK : ret(v);
    }
    case "add":
      return bind(evalE(e.a, env), (a) =>
        bind(evalE(e.b, env), (b) =>
          a.tag === "int" && b.tag === "int" ? ret({ tag: "int", n: a.n + b.n }) : STUCK,
        ),
      );
    case "let":
      return bind(evalE(e.e1, env), (v) => evalE(e.e2, [v, ...env]));
    case "perform":
      // capture the current continuation (the `k` bind threads in) and yield
      return bind(evalE(e.arg, env), (p) => ({ tag: "op", payload: p, k: (w) => ret(w) }));
    case "handle":
      return handle(evalE(e.body, env), e.clause, env);
    case "resume":
      return bind(evalE(e.k, env), (kv) =>
        bind(evalE(e.v, env), (w) => (kv.tag === "cont" ? kv.resume(w) : STUCK)),
      );
  }
}

// Run a closed program. A standing `op` (perform with no enclosing handler) or a
// `stuck` both report as notok -- matching `run`'s `none` (out-of-fuel or stuck).
export function runReify(e: E): { ok: true; value: RVal } | { ok: false } {
  const c = evalE(e, []);
  if (c.tag !== "ret") return { ok: false };
  return { ok: true, value: c.v.tag === "int" ? { v: "int", n: c.v.n } : { v: "cont" } };
}
