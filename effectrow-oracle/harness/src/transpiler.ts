// transpiler.ts -- THE CODE UNDER TEST.
//
// Replace the body of `unify` with a call into bang-lang's actual effect-row
// unifier (the one in your Effect TS transpiler). The differential test drives
// THIS against the verified oracle.
//
// The default implementation here is a deliberately independent re-derivation
// (not a copy of rowalg.ts) so the test is meaningful. Flip BUG_DEMO to true to
// watch the harness catch a subtle wrong answer.

import { type Row, type Subst, canon, diff, subset } from "./rowalg.js";

const BUG_DEMO = false;

export function unify(fresh: number, r1in: Row, r2in: Row): Subst | null {
  const r1: Row = { labels: canon(r1in.labels), tail: r1in.tail };
  const r2: Row = { labels: canon(r2in.labels), tail: r2in.tail };

  if (r1.tail === null && r2.tail === null) {
    return arrEq(r1.labels, r2.labels) ? [] : null;
  }
  if (r1.tail !== null && r2.tail === null) {
    if (!subset(r1.labels, r2.labels)) return null;
    return [[r1.tail, { labels: diff(r2.labels, r1.labels), tail: null }]];
  }
  if (r1.tail === null && r2.tail !== null) {
    if (!subset(r2.labels, r1.labels)) return null;
    return [[r2.tail, { labels: diff(r1.labels, r2.labels), tail: null }]];
  }
  // open / open
  const v1 = r1.tail as number, v2 = r2.tail as number;
  if (v1 === v2) return arrEq(r1.labels, r2.labels) ? [] : null;

  const only2 = diff(r2.labels, r1.labels);
  const only1 = diff(r1.labels, r2.labels);
  if (BUG_DEMO) {
    // subtle bug: forgets to extend r2 with r1's exclusive labels
    return [[v1, { labels: only2, tail: fresh }]];
  }
  return [
    [v1, { labels: only2, tail: fresh }],
    [v2, { labels: only1, tail: fresh }],
  ];
}

const arrEq = (a: number[], b: number[]) =>
  a.length === b.length && a.every((x, i) => x === b[i]);
