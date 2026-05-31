// rowalg.ts -- TypeScript reference row algebra.
//
// Mirrors oracle/src/Bang.EffectRow.fst. Used for (a) the semilattice law
// tests and (b) comparing transpiler vs oracle results by DENOTATION rather
// than by syntactic substitution. tools/selfcheck.mjs re-implements the same
// operations a third time and cross-checks them, so this logic is de-risked.

export type Label = number;
export type RVar = number;
export interface Row { labels: Label[]; tail: RVar | null }
export type Subst = [RVar, Row][];

export const mem = (x: Label, l: Label[]): boolean => l.includes(x);

export function insert(x: Label, l: Label[]): Label[] {
  const out: Label[] = [];
  let placed = false;
  for (const h of l) {
    if (!placed && x < h) { out.push(x); placed = true; }
    if (x === h) { placed = true; }   // idempotence: skip duplicate
    out.push(h);
  }
  if (!placed) out.push(x);
  return out;
}

export const union = (a: Label[], b: Label[]): Label[] =>
  a.reduceRight((acc, x) => insert(x, acc), b.slice());

export const diff = (a: Label[], b: Label[]): Label[] =>
  a.reduceRight((acc, x) => (mem(x, b) ? acc : insert(x, acc)), [] as Label[]);

// canonical normal form: sorted + dedup == union with empty
export const canon = (l: Label[]): Label[] => union(l, []);

export const subset = (a: Label[], b: Label[]): boolean => a.every((x) => mem(x, b));

// on canonical rows this equals structural array equality, but we keep the
// extensional definition for the denotation comparison.
export const rowEq = (a: Label[], b: Label[]): boolean => subset(a, b) && subset(b, a);

export function applyR(fuel: number, s: Subst, r: Row): Row {
  if (r.tail === null) return r;
  if (fuel <= 0) return r;
  const found = s.find(([k]) => k === r.tail);
  if (!found) return r;
  const rr = applyR(fuel - 1, s, found[1]);
  return { labels: union(r.labels, rr.labels), tail: rr.tail };
}

// Compare two unification *results* by denotation, quotienting by the choice
// of fresh tail variable. This is the subtle bit: both sides invent fresh
// vars with different names, so a syntactic subst comparison fails on correct
// results. We apply each side's subst to both input rows and compare.
export function sameResult(
  r1: Row, r2: Row,
  a: Subst | null, b: Subst | null,
): boolean {
  if (a === null || b === null) return a === b;          // both must fail, or both succeed
  const fuel = Math.max(a.length, b.length) + 2;
  const a1 = applyR(fuel, a, r1), a2 = applyR(fuel, a, r2);
  const b1 = applyR(fuel, b, r1), b2 = applyR(fuel, b, r2);
  // each side must internally unify its two rows...
  const aOk = rowEq(a1.labels, a2.labels) && a1.tail === a2.tail;
  const bOk = rowEq(b1.labels, b2.labels) && b1.tail === b2.tail;
  if (!aOk || !bOk) return false;
  // ...and the two sides must agree on the denotation they unified to,
  // modulo the fresh-var name (compare label set; tail null-vs-var distinction
  // is what matters, exact var id is alpha-renameable).
  const tailShape = (t: RVar | null) => (t === null ? "closed" : "open");
  return rowEq(a1.labels, b1.labels) && tailShape(a1.tail) === tailShape(b1.tail);
}
