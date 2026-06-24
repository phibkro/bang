# Effect-handler dispatch × verification — the landscape, and consequences for bang-lang

> Source: a fact-checked deep-research sweep (2026-06-25, workflow `wf_60f94539-140`; 107 agents,
> 3-vote adversarial verification). Each approach is assessed against bang-lang's load-bearing
> invariants: **(1)** dynamic/ambient dispatch · **(2)** effect rows as SETS · **(3)** calculated VM
> over an UNTYPED executable oracle · **(4)** untyped step-indexed BIORTHOGONAL LR · **(5)** 5 kernel
> primitives · **(6)** `no_accidental_handling` 0-axiom. The through-line: does the approach
> **dissolve**, **close**, or **leave** the resume-through-a-wrap edge (ADR-0043), and at what cost?

## Headline finding — our edge is a real frontier gap

The two axes are **coupled**: every approach that *dissolves* the resume-through-a-wrap / accidental-handling
problem **by construction** does so by making handler identity **STATIC and lexical** — trading away invariant
(1) — and, in every *proven* case, riding a **typed** capability/effect discipline (the typed shadow bang-lang
deliberately avoids). The one posture that stays untyped + dynamic and still side-steps the answer-type
obstruction (Hazel/HH protocols) is **Iris/Coq-native and one-shot only** — and our edge lives in the
*multi-shot* setting. **No surveyed source exhibits an untyped, Nat-step-indexed, multi-shot biorthogonal LR
that closes the edge.** That exact intersection is the gap our seam sits in — it is the frontier, not an
oversight.

## Axis A — dispatch disciplines

### Dynamic / ambient dispatch — *ours* (Eff, OCaml 5, Koka default, Hazel/HH)
A perform searches the runtime handler stack outward for the nearest matching handler. **Consequence:** this
*is* invariant (1); the resume-edge and accidental-handling are properties it must **prove** (we prove
`no_accidental_handling` 0-axiom via lacks-constraints) rather than get for free. The edge **stays** (tested).

### Lexical handlers — Lexa (Ma et al., OOPSLA'24) · `[high]`
Handler resolved like a lexically-scoped variable; **no outward stack-walk**, resumption captured directly;
Biernacki's `lift` becomes unnecessary. **Consequence for bang-lang:** structurally **CLOSES** the edge — but
drops invariant (1) (a paradigm change), and the *proven* abstraction-safety in this lineage leans on a
type-and-effect discipline (Lexa's IL is untyped, but the formal guarantee assumes typing). [lexa-oopsla2024]

### Zero-overhead lexical — clue/hopper (Ma et al., OOPSLA'25) · `[high]`
A **type-directed** stack walk via statically pre-computed provenance tables; reifies NO runtime handler
labels. Closest to our runtime *shape* (it still walks a stack), but the walk is computed **from typing**.
**Consequence:** does not carry to our untyped oracle (3) without a typed translation. [zero-oopsla2025]

### Tunneling — Zhang & Myers (POPL'19) · `[high]`
A handler is supplied at every operation site and resolved to the nearest **lexically** enclosing binding,
fixed by substitution; effects "tunnel through" intermediary handlers. Structurally eliminates accidental
handling + restores Reynolds parametricity. **Consequence:** the canonical by-construction version of the
property we prove with lacks-constraints + tests — but requires lexical/named dispatch (drops (1)). It is the
conceptual root of our `no_accidental_handling`. [abseff-popl2019]

### Capability-passing — Effekt (Brachthäuser et al.) · `[medium]`
Effect operations are methods on **capability objects passed as explicit arguments**; resolution is
lexical/static, eliminating the runtime handler stack entirely. **Consequence:** by-construction
no-accidental-handling, but it removes the dynamic handler stack (drops (1)) and reshapes the kernel away from
the 5-primitive dynamic-handler model. **⚠ Refuted (vote 1–2):** the stronger claim that capability-passing
*alone* (from a polymorphic function's type) guarantees effect parametricity does NOT hold — the guarantee is
not free from the type. [effekt CUP]

### Deep vs shallow handlers (Hillerström–Lindley) · `[high]`
Orthogonal "flavour" axis: deep = folds over computation trees, shallow = case-splits. **Inter-encodable** —
deep simulate shallow via a *local term-level* translation. **Consequence (good news for (5)):** our DEEP
kernel can express shallow behaviour **without a 6th primitive**, at a performance cost; the encoding is
type-directed (extra verification effort over an untyped oracle, but the expressivity holds). [shallow-extended]

## Axis B — verification techniques

### Forward simulation (Lexa→Salt, Zero-Lexa SL→TL, AsmFX) · `[high]`
Verify **translation** semantics-preservation, NOT program contextual equivalence — so they **never confront**
the captured-continuation answer-type obstruction. **Consequence:** they don't transfer to our goal. They are
also all type-directed (config-matching / capture-sets-from-typing / a VALIDITY predicate substituting for the
typing a LR would need). Useful for *compiler correctness* (our `compile_forward_sim` is this family), useless
for *contextual equivalence*. [lexa-oopsla2024]

### Hazel/HH protocols — de Vilhena & Pottier · `[high]` — THE most aligned near-miss
HH is **UNTYPED** with a single unnamed effect handled by the **nearest enclosing handler** (dynamic dispatch —
matches (1) + the untyped oracle). It reasons via **PROTOCOLS**: a behavioral request/reply spec where, for
every protocol-permitted reply `w`, plugging `w` into the captured context `N` yields `N[w]` still obeying the
SAME protocol. **This specifies the captured continuation WITHOUT recovering its answer type** — a genuine route
around our no-related⇒typing obstruction. **BUT:** it is **Iris/Coq-native** (not Nat-step-indexed
Lean-portable) and restricted to **ONE-SHOT** continuations — and our edge is the **multi-shot/resumptive**
case. So it is the most promising *idea* (behavioral continuation spec, not type recovery), gated by two real
gaps (portability + multi-shot). [hazel SL]

### Nat-step-indexed biorthogonal — Matache 2019 · `[high]`
The exact technique-family we use IS demonstrated **Lean-portably** for an algebraic-effects CPS language
(N-indexed families, ⊤⊤-closure, an explicit biorthogonal stack relation). **BUT there it is TYPED** — value
relations indexed by source types, the stack relation by typed stacks — so it assumes typing throughout and
never hits our obstruction. **Consequence:** confirms our architecture is sound and Lean-portable; confirms the
obstruction is *specifically* the untyped variant; and confirms no one has published the untyped multi-shot
form. [arxiv 1902.04645]

## Consequences for our decisions

1. **Validates the static-link-kernel direction (ADR-0044, the dispatch spike, task #13) — with a sharp
   caveat.** Every dissolve-the-edge result confirms *static handler identity removes the search and the edge*.
   That is exactly the "kernel = static-link, dynamic-search = shell" hypothesis. **The caveat the research
   adds:** every *proven* static approach rides a **typed** discipline. So the spike's real question sharpens
   to: *can a static-link dispatch dissolve the edge in our UNTYPED kernel without importing the typed shadow?*
   If yes, it's a genuinely new point (untyped + static + dynamic-as-derived-shell). If the typing turns out
   load-bearing even for static, the spike says so cheaply.
2. **A second, untyped route exists and was previously underweighted: Hazel/HH PROTOCOLS.** Specifying the
   captured continuation *behaviorally* (reply-obeys-protocol) instead of recovering its answer type is the one
   untyped-dynamic technique that side-steps our exact obstruction. Its blockers (Iris→Lean Nat-step port;
   one-shot→multi-shot) are real but are *different* blockers than the typed reshape — worth a scoped feasibility
   look as an alternative to both the typed-CrelK reshape (NO-GO) and the static-kernel pivot.
3. **Deep-as-shallow is free of a 6th primitive (5).** If we ever want shallow handlers, the deep kernel encodes
   them via a local term-level translation — no kernel growth.
4. **Compiler-correctness forward simulation (our `compile_forward_sim`) is the right tool for ◊5 and the wrong
   tool for the edge** — confirmed: it proves translation preservation, never contextual equivalence.

## The map, in one line

```
dissolve the edge  ⟺  static/lexical dispatch (drop invariant 1)  ⟺  proven only WITH typing
stay untyped+dynamic + side-step the edge  ⟺  Hazel protocols  ⟺  Iris-native + one-shot
our setting (untyped + Nat-step + multi-shot + biorthogonal)  ⟺  the open frontier — our seam
```

So: the seam is the honest cost of being **the only one in the untyped-dynamic-multi-shot cell**. The two
escape routes are (a) go static (the kernel/shell-pivot — validated direction, spike pending) or (b) port the
Hazel protocol idea to Nat-step + multi-shot (a harder, more novel research bet). Both are now *named and
scoped*, not vague.

*Cited from the verified deep-research sweep; primary sources linked inline. See ADR-0043 (the edge), ADR-0044
(dynamic vs lexical), and the queued static-link dispatch spike (task #13).*
