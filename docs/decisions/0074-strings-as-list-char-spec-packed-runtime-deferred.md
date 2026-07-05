# ADR-0074 · Strings: `String = List Char` verified spec, Char = a code point; packed runtime + normalization deferred behind the oracle

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: `String` is the inductive spec `List Char`, `Char` a Unicode code point (a distinct type over `Int`, refined once Q31 lands). All string operations are TOTAL structural folds (certified ⊥ by #47) — CORRECT and slow first (invariant #7). It is LIBRARY code over the kernel (rides `data` + `Int`; invariant #5 — no 6th primitive); only surface string/char literals need parser support. A packed UTF-8 runtime representation is DEFERRED — a later compiled OPTIMIZATION differentially-bridged to the `List Char` ORACLE (the exact ADR-0067 `Int`-spec-behind-the-oracle move). Unicode normalization + grapheme clusters are DEFERRED as documented non-features (not silent gaps).
- **Depends-on**: 0067, 0069
- **Relates-to**: Q31 (Char as a refined code point), #47 (total folds), #48 (effectful-recursion limit — string ops are pure so unaffected)

- **Status:** Accepted (operator-approved 2026-07-06)
- **Date:** 2026-07-06
- **Layer:** C + library (surface literals + a `List Char` stdlib; no kernel, no verification-spine change)
- **Builds on:** ADR-0067 (Int = unbounded ℤ *spec* with the runtime width *behind the oracle* — this is
  the SAME stratification, one type over), ADR-0069 (`data` decls — `List`/`Char` are data), #47 (the
  structural termination checker — makes `List Char` folds total for free). Precedent: Lean's own
  `String` is `structure String where data : List Char`, compiled to a packed UTF-8 object.

## Context

Strings are the last gap to "bang writes its own tools" (a tokenizer, a calculator interpreter — the
dogfood verdict was "no recursion, no strings"; recursion landed via ADR-0073). Strings are the
TEXTBOOK correctness-vs-performance tension: the correct model (an inductive list of characters — total,
reasoned-about) is O(n)/list-memory slow; the fast model (a packed UTF-8 byte buffer / rope) is not
inductive. The question is how to get both without trading one for the other.

## Decision

Resolve the tension with BANG's signature stratification — **verified spec + fast runtime + differential
bridge** — exactly as `Source.eval` ↔ the compiled machine, and ADR-0067's `Int`:

```
SPEC (verified, canonical)   String = List Char            total structural-fold ops (#47),
                             Char  = a code point           the reasoning model + the ORACLE
RUNTIME (fast, DEFERRED)     packed UTF-8 buffer / rope     O(1) length, cache-friendly
BRIDGE                       differential test vs the       the fast rep is "correct" only because
                             List-Char oracle               it is checked against the spec
```

1. **`String = List Char`** — an inductive spec (rides ADR-0069 `data`: `data List = Nil | Cons(Char,
   List)`). Every op (`length`, `concat`, `reverse`, `map`, `split`) is a TOTAL structural fold —
   certified ⊥ by #47 (structural recursion on the list). String ops are pure, so #48's
   effectful-recursion limit does not bite.
2. **`Char` = a Unicode CODE POINT** (Rust's `char` model: a scalar value), a type DISTINCT from `Int`
   (`data Char = Char(Int)` newtype now, for type distinction — you can't mix a char and a number;
   becomes the refined `{n : Int // n ≤ 0x10FFFF ∧ ¬surrogate}` when Q31 refinement lands, validity
   behind the oracle until then — the ADR-0067 permissive-spec pattern).
3. **LIBRARY over the kernel — invariant #5 holds, NO 6th primitive.** `String`/`Char` are `data` +
   `Int`. The only kernel-adjacent work is SURFACE: string literals `"hi"` (desugar to `Cons(Char 104,
   Cons(Char 105, Nil))`) and char literals `'a'` — parser support like `let rec` needed.
4. **Correct-and-slow FIRST (invariant #7).** Ship the `List Char` spec + stdlib ops; DEFER the packed
   UTF-8 runtime as a later compiled optimization, differentially-bridged to the `List Char` oracle
   (ops on the packed rep must AGREE with the spec). The spec stays canonical.
5. **DEFER Unicode normalization + grapheme clusters** — documented NON-FEATURES (a spec Non-Features
   entry), not silent gaps. v1 = code-point semantics.

## Rejected / not-now

- **`Char` = byte (`Word8`)** — simple but NOT Unicode-correct (a character ≠ a byte in UTF-8). Rejected.
- **`Char` = grapheme cluster** (Swift's model) — most user-correct but most complex (extended grapheme
  segmentation). DEFERRED, not v1.
- **`String` as a KERNEL primitive** (a packed-bytes builtin) — violates invariant #5 (no 6th primitive)
  and #8 (the calculated VM is canonical); strings are library code.
- **Packed-runtime FIRST** — violates invariant #7 (a slow correct path beats a fast unverified one);
  the fast rep with no oracle behind it is exactly the anti-pattern (invariant #1: proof rides the
  reference).

## Consequences

- **Intrinsic Unicode tension is NOT bang's to fully solve.** Code-point indexing is O(n) in UTF-8
  (variable width — this is why Rust forces byte-indices + iterators); v1 has code-point semantics and
  DEFERS byte-index performance + normalization. Documented, not hidden.
- The packed-runtime bridge is future work — until then strings are O(n)/list-memory (fine for a
  tokenizer on small inputs; invariant #7 says that is correct-first).
- Char refinement (validity) rides Q31 — until refinement lands, an out-of-range `Int` code point is
  representable (permissive spec, ADR-0067 pattern).

## Revisit if

- A real perf need on strings bites (large inputs) → build the packed UTF-8 runtime + the differential
  bridge (the deferred optimization).
- Q31 refinement types land → `Char` becomes the refined code point (validity by construction).
- Grapheme-correct or normalization-sensitive text handling becomes a use case → lift from code points.
