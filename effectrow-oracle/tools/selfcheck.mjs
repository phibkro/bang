// selfcheck.mjs -- zero-dependency third implementation + property checks.
//
// Purpose: de-risk the DESIGN before any F*/OCaml/TS toolchain is installed.
// If this passes, the F* lemmas (`canon_unique`, `unify_sound`) are stated over
// an algorithm that empirically holds, and the harness's denotation comparison
// is known to (a) accept alpha-renamed-equal results and (b) catch real bugs.
//
// Run: node tools/selfcheck.mjs

// ---- deterministic PRNG (mulberry32) so failures are reproducible ----------
function rng(seed) {
  return () => {
    seed |= 0; seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// ---- third implementation of the row algebra -------------------------------
const mem = (x, l) => l.includes(x);
function insert(x, l) {
  const out = []; let placed = false;
  for (const h of l) {
    if (!placed && x < h) { out.push(x); placed = true; }
    if (x === h) placed = true;
    out.push(h);
  }
  if (!placed) out.push(x);
  return out;
}
const union = (a, b) => a.slice().reverse().reduce((acc, x) => insert(x, acc), b.slice());
const diff = (a, b) => a.slice().reverse().reduce((acc, x) => (mem(x, b) ? acc : insert(x, acc)), []);
const canon = (l) => union(l, []);
const subset = (a, b) => a.every((x) => mem(x, b));
const rowEq = (a, b) => subset(a, b) && subset(b, a);
const arrEq = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);

function applyR(fuel, s, r) {
  if (r.tail === null) return r;
  if (fuel <= 0) return r;
  const f = s.find(([k]) => k === r.tail);
  if (!f) return r;
  const rr = applyR(fuel - 1, s, f[1]);
  return { labels: union(r.labels, rr.labels), tail: rr.tail };
}

// the ORACLE semantics (what Bang.EffectRow.fst specifies)
function unify(fresh, r1, r2) {
  r1 = { labels: canon(r1.labels), tail: r1.tail };
  r2 = { labels: canon(r2.labels), tail: r2.tail };
  if (r1.tail === null && r2.tail === null) return arrEq(r1.labels, r2.labels) ? [] : null;
  if (r1.tail !== null && r2.tail === null)
    return subset(r1.labels, r2.labels) ? [[r1.tail, { labels: diff(r2.labels, r1.labels), tail: null }]] : null;
  if (r1.tail === null && r2.tail !== null)
    return subset(r2.labels, r1.labels) ? [[r2.tail, { labels: diff(r1.labels, r2.labels), tail: null }]] : null;
  const v1 = r1.tail, v2 = r2.tail;
  if (v1 === v2) return arrEq(r1.labels, r2.labels) ? [] : null;
  return [
    [v1, { labels: diff(r2.labels, r1.labels), tail: fresh }],
    [v2, { labels: diff(r1.labels, r2.labels), tail: fresh }],
  ];
}

// a BUGGY transpiler: open/open forgets to extend the second tail
function unifyBuggy(fresh, r1, r2) {
  const r = unify(fresh, r1, r2);
  if (r && r.length === 2) return [r[0]]; // drop the second binding
  return r;
}

function sameResult(r1, r2, a, b) {
  if (a === null || b === null) return a === b;
  const fuel = Math.max(a.length, b.length) + 2;
  const a1 = applyR(fuel, a, r1), a2 = applyR(fuel, a, r2);
  const b1 = applyR(fuel, b, r1), b2 = applyR(fuel, b, r2);
  const aOk = rowEq(a1.labels, a2.labels) && a1.tail === a2.tail;
  const bOk = rowEq(b1.labels, b2.labels) && b1.tail === b2.tail;
  if (!aOk || !bOk) return false;
  const shape = (t) => (t === null ? "closed" : "open");
  return rowEq(a1.labels, b1.labels) && shape(a1.tail) === shape(b1.tail);
}

// ---- generators ------------------------------------------------------------
function randLabels(rand) {
  const n = Math.floor(rand() * 7);
  const s = new Set();
  for (let i = 0; i < n; i++) s.add(Math.floor(rand() * 32));
  return [...s].sort((a, b) => a - b);
}
function randRow(rand) {
  return { labels: randLabels(rand), tail: rand() < 0.5 ? null : Math.floor(rand() * 5) };
}

// ---- harness ---------------------------------------------------------------
let fails = 0;
const N = 20000;
const FRESH = 999;
function check(name, cond, ctx) {
  if (!cond) { fails++; console.error(`FAIL ${name}  ${ctx ?? ""}`); }
}

const rand = rng(0xC0FFEE);

// 1. semilattice laws of union
for (let i = 0; i < N; i++) {
  const a = randLabels(rand), b = randLabels(rand), c = randLabels(rand);
  check("commutative", arrEq(union(a, b), union(b, a)), JSON.stringify([a, b]));
  check("idempotent", arrEq(union(a, a), canon(a)), JSON.stringify(a));
  check("associative", arrEq(union(a, union(b, c)), union(union(a, b), c)), JSON.stringify([a, b, c]));
  check("identity", arrEq(union(a, []), canon(a)), JSON.stringify(a));
}

// 2. canon idempotent + order-insensitive
for (let i = 0; i < N; i++) {
  const a = randLabels(rand);
  const shuffled = a.slice().reverse();
  check("canon-idem", arrEq(canon(canon(a)), canon(a)), JSON.stringify(a));
  check("canon-order", arrEq(canon(shuffled), canon(a)), JSON.stringify(a));
}

// 3. KEYSTONE canon_unique: on canonical rows, rowEq => array equality
for (let i = 0; i < N; i++) {
  const a = randLabels(rand), b = randLabels(rand); // already canonical
  if (rowEq(a, b)) check("canon_unique", arrEq(a, b), JSON.stringify([a, b]));
}

// 4. unify_sound: when the oracle says yes, applying the subst makes the two
//    rows denote the same label set and agree on tail.
let unifiedCount = 0;
for (let i = 0; i < N; i++) {
  const r1 = randRow(rand), r2 = randRow(rand);
  const s = unify(FRESH, r1, r2);
  if (s !== null) {
    unifiedCount++;
    const fuel = s.length + 2;
    const x1 = applyR(fuel, s, r1), x2 = applyR(fuel, s, r2);
    check("unify_sound:labels", rowEq(x1.labels, x2.labels), JSON.stringify([r1, r2, s]));
    check("unify_sound:tail", x1.tail === x2.tail, JSON.stringify([r1, r2, s]));
  }
}

// 5. sameResult accepts a CORRECT independent transpiler (alpha-rename of fresh)
//    and CATCHES the buggy one at least on some open/open case.
let buggyCaught = 0, goodAgree = 0, openOpen = 0;
for (let i = 0; i < N; i++) {
  const r1 = randRow(rand), r2 = randRow(rand);
  const truth = unify(FRESH, r1, r2);
  const good = unify(1234, r1, r2);           // different fresh var name on purpose
  const bad = unifyBuggy(1234, r1, r2);
  if (sameResult(r1, r2, good, truth)) goodAgree++;
  else check("good-transpiler-agrees", false, JSON.stringify([r1, r2]));
  if (r1.tail !== null && r2.tail !== null && r1.tail !== r2.tail
      && !arrEq(canon(r1.labels), canon(r2.labels))) {
    openOpen++;
    if (!sameResult(r1, r2, bad, truth)) buggyCaught++;
  }
}

console.log(`unify succeeded on ${unifiedCount}/${N} pairs`);
console.log(`good transpiler agreed on ${goodAgree}/${N} (with renamed fresh var)`);
console.log(`open/open non-equal cases: ${openOpen}; buggy transpiler caught on ${buggyCaught}`);
check("bug-is-actually-caught", openOpen > 0 && buggyCaught > 0, `caught ${buggyCaught}/${openOpen}`);

if (fails === 0) {
  console.log("\nALL CHECKS PASSED");
  process.exit(0);
} else {
  console.error(`\n${fails} CHECK(S) FAILED`);
  process.exit(1);
}
