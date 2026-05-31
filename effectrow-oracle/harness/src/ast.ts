// ast.ts -- builders for the BANG core AST and a compact wire/result shape.
//
// Mirrors the JSON the Lean `eval` oracle parses (Bang/EvalJson.lean) and the
// candidate evaluator consumes. Keeping one builder module means the golden
// programs are written once and fed to BOTH the oracle and the candidate.

export type Pat =
  | { p: "wild" }
  | { p: "var"; x: string }
  | { p: "lit"; v: number }
  | { p: "con"; c: string; args: Pat[] };

export type Hspec =
  | { h: "state"; label: number; init: Expr }
  | { h: "throws"; label: number };

export type Expr =
  | { t: "lit"; v: number }
  | { t: "unit" }
  | { t: "var"; x: string }
  | { t: "lam"; x: string; body: Expr }
  | { t: "app"; f: Expr; a: Expr }
  | { t: "thunk"; e: Expr }
  | { t: "force"; e: Expr }
  | { t: "let"; x: string; e1: Expr; e2: Expr }
  | { t: "con"; c: string; args: Expr[] }
  | { t: "match"; scrut: Expr; arms: { pat: Pat; rhs: Expr }[] }
  | { t: "if"; c: Expr; then: Expr; else: Expr }
  | { t: "binop"; op: string; a: Expr; b: Expr }
  | { t: "perform"; label: number; op: string; arg: Expr }
  | { t: "handle"; h: Hspec; body: Expr };

// --- expression builders ---
export const lit = (v: number): Expr => ({ t: "lit", v });
export const unit: Expr = { t: "unit" };
export const v = (x: string): Expr => ({ t: "var", x });
export const lam = (x: string, body: Expr): Expr => ({ t: "lam", x, body });
export const app = (f: Expr, a: Expr): Expr => ({ t: "app", f, a });
export const thunk = (e: Expr): Expr => ({ t: "thunk", e });
export const force = (e: Expr): Expr => ({ t: "force", e });
export const letE = (x: string, e1: Expr, e2: Expr): Expr => ({ t: "let", x, e1, e2 });
export const con = (c: string, args: Expr[] = []): Expr => ({ t: "con", c, args });
export const matchE = (scrut: Expr, arms: [Pat, Expr][]): Expr =>
  ({ t: "match", scrut, arms: arms.map(([pat, rhs]) => ({ pat, rhs })) });
export const ifE = (c: Expr, then_: Expr, else_: Expr): Expr =>
  ({ t: "if", c, then: then_, else: else_ });
export const binop = (op: string, a: Expr, b: Expr): Expr => ({ t: "binop", op, a, b });
export const perform = (label: number, op: string, arg: Expr = unit): Expr =>
  ({ t: "perform", label, op, arg });
export const handle = (h: Hspec, body: Expr): Expr => ({ t: "handle", h, body });

// --- pattern builders ---
export const pwild: Pat = { p: "wild" };
export const pvar = (x: string): Pat => ({ p: "var", x });
export const plit = (v: number): Pat => ({ p: "lit", v });
export const pcon = (c: string, args: Pat[] = []): Pat => ({ p: "con", c, args });

// --- handler builders ---
export const stateH = (label: number, init: Expr): Hspec => ({ h: "state", label, init });
export const throwsH = (label: number): Hspec => ({ h: "throws", label });

// --- derived sugar ---
// Sequence two computations: force `a` (running its effects, discarding its WHNF
// value), then evaluate `b`. Encoded with a wildcard match, which forces its
// scrutinee — no dedicated AST node needed (matches the Lean semantics exactly).
export const seq = (a: Expr, b: Expr): Expr => matchE(a, [[pwild, b]]);
export const get = (label: number): Expr => perform(label, "get");
export const put = (label: number, e: Expr): Expr => perform(label, "put", e);
export const raise = (label: number, e: Expr): Expr => perform(label, "raise", e);

// --- result shape (what both the oracle and candidate return) ---
export type Value =
  | { v: "int"; n: number }
  | { v: "unit" }
  | { v: "con"; c: string; args: Value[] }
  | { v: "clos" }
  | { v: "thunk" };

export type RunResult =
  | { ok: true; value: Value }
  | { ok: false; reason: "outOfFuel" }
  | { ok: false; reason: "stuck"; msg: string }
  | { ok: false; reason: "uncaught"; label: number; effOp: string };
