---
type: design-question
title: "module ≟ trait ≟ effect ≟ capability: one interface+implementation construct, dialed by resumption grade?"
description: "deep unification; stress-test, don't decide a priori"
status: open
area: effects
ties: ["Q27", "Q34", "Q37", "ADR-0068"]
see-also: ["#44", "#35", "#36"]
---
**Question**: are module, trait, effect, and capability FOUR constructs or ONE? They are all
**interface + implementation (+ laws)** — the fundamental abstraction boundary. bang's OWN vocabulary says
so: a handler is "a value implementing an effect's operations"; a trait `impl` is "a value implementing a
trait's operations" — the same sentence. The question is whether the differences warrant separate
constructs or fit as KNOBS on one.

**Why it matters**: "one construct per problem" — if trait/effect/module/capability unify into a single
signature-and-implementation construct, that's a large simplification (one surface, one resolution story,
one law mechanism). It bears on BOTH the module system ([[Q34]]) and the effect system at once — deciding
it wrong duplicates the abstraction boundary twice.

**The convergence — they share the interface; the AXES that differ:**
```
axis              module / trait                     effect
──────────────────────────────────────────────────────────────────────────────
interface         typed ops (+ laws)                 typed ops (+ laws)        ← IDENTICAL
binding time      STATIC (resolved by type / import) DYNAMIC (handler installed at the use site)
impl receives     its arguments                      arguments + the delimited CONTINUATION
RESUMPTION GRADE  grade-1 (returns exactly once)     ANY grade (resume 0 / 1 / many)  ← the KEY axis (Q27)
multiplicity      one binding ACTIVE per use site    many handlers COEXIST, lexically scoped
                  (may have many impls, one active)  (`state 1 as a in (state 2 as b in …)`)
tracked in types  a trait bound  (`Monoid a =>`)     the effect ROW  (`{State}`)
```

**The unifying KNOB = RESUMPTION GRADE (Q27) + continuation-access (operator's insight).** A trait/module
is the **resumption-grade-1, no-continuation, statically-bound** special case; a general effect is ANY
grade WITH continuation access, dynamically installed. The grade is the DIAL between them — which makes the
unification plausible, not just a rhyme. Multiplicity is COEXISTENCE (many handlers live-and-scoped at
once), not cardinality (modules can have many impls, one active per site — operator's correction).

**The capability convergence (closes [[Q37]]'s loop)**: handler = capability = dictionary you're handed =
module-instance. All the same object from different angles — "the type system carrying capabilities" is
this convergence seen from the row.

**Resolution METHOD — STRESS-TEST, don't decide a priori (operator's directive)**: try to express traits
AND effects as ONE construct (interface + implementation, parameterized by grade + continuation +
binding-time). See whether the resumption/continuation difference fits as a KNOB or genuinely BREAKS the
unification. The continuation axis is the real risk — a static call CANNOT resume, so the unification is
clean at the INTERFACE level and needs care at the IMPLEMENTATION level. Build-and-see, the bang way (like
recursion-needs-no-primitive was a re-spike, not an assertion).

**Prior art (this is not a fantasy)**: **Effekt** (Brachthäuser) — effects compile to capability/dictionary
passing (effects ≈ capabilities ≈ type-class dictionaries); **1ML** (Rossberg) — modules as first-class
values; the type-classes-as-implicit-effects line (Scala 3 given/using).

**Blocked on**: not blocked — a design+stress-test, doable incrementally (bang already has BOTH ends: traits
= static grade-1, effects = dynamic any-grade). Best done WHEN the module system is built ([[Q34]]) or #44
(user-defined effects) is taken up — so the unification is tested against a real second construct, not in
the abstract.

**Revisit signal**: the module system is designed ([[Q34]]) → decide whether it's a new construct or the
trait/effect construct dialed to static; OR #44 (user-defined effects) is built → the effect-declaration
surface either matches the trait surface (unify) or diverges (keep separate, document why). Ties [[Q27
grade axis]] (the unifying knob), [[Q34 module system]], [[Q37 FFI as effect]] (capability = handler),
#44 (user-defined effects), ADR-0068 (traits + laws — the shared law mechanism), #35/#36 (resumption
grades).
