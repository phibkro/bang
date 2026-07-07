---
type: design-question
title: "Compilation strategy for the dynamic escape hatch — static-first; dispatch cold, JIT-monomorphize hot"
description: "Stay static (AOT elaborate-to-mono) by default for perf + static analysis + compile-time soundness; for runtime-known types, dispatch one-offs cheaply and JIT-monomorphize ONLY hot+type-stable sites (tiered, profile-guided); JIT-mono = the same elaborate-to-mono run late, still targeting the verified kernel"
status: open
area: tooling
ties: ["Q37", "Q39", "ADR-0080", "ADR-0075"]
see-also: ["Julia (runtime monomorphization)", "V8 inline caches (mono→poly→megamorphic)", "HotSpot/PyPy tiered compilation", "invariant #7 (performance second-class)", "◊5 compiled path (WasmFX)"]
---

**Question**: what is the compilation strategy for the DYNAMIC escape hatch — the cases where a value's
concrete type is only known at RUNTIME (existentials / `dyn Trait`, runtime-loaded code)? bang stays STATIC
by default (AOT elaborate-to-mono, ADR-0075: performance + static analysis + compile-time soundness, all
from monomorphization). Dynamic is the escape hatch (Q37 existentials). The question is HOW to compile it.

**Key distinction (established): "dynamic" and "slow" are DIFFERENT axes.** Dispatch (a vtable/dictionary)
trades speed for flexibility — an indirect call, no inlining across it. But **JIT-MONOMORPHIZATION** buys
the flexibility AND keeps the speed: when the concrete type becomes known at runtime, COMPILE a specialized
(monomorphic) copy for it — runtime compilation INSTEAD of runtime dispatch. Real: Julia (dynamically-typed
surface, JIT-specializes a monomorphic method per concrete arg-type combo), V8 inline caches (specialize +
inline per observed shape), .NET reified generics. NB safety: dispatch is already safe WITHOUT a JIT (the
dictionary is type-correct; boundary input is validated) — JIT-mono is a PERFORMANCE technique, not a
safety one (and a JIT is a LARGER trusted surface).

**The recommended strategy — TIERED, static-first (operator's refinement):**
```
static (AOT-mono)   the DEFAULT — compile-time-known types → monomorphic kernel terms      [bang today: bite-1/bite-2]
dynamic escape (runtime-known type):
  Tier 0  DISPATCH   a dictionary/vtable — cheap, no compile cost → right for COLD / one-off / run-once sites
  Tier 1  JIT-MONO   runtime-specialize to kernel terms — pay the compile cost ONLY when the site is HOT
                     AND type-stable (the pattern repeats), so it amortizes
  megamorphic (a site that sees MANY types) → stays on DISPATCH (JIT-mono would explode code)
```
Threshold = **hotness × type-stability** (profile-guided graduation — exactly HotSpot/V8/PyPy: cheap tier
first, specialize only the hot paths). Dispatch amortizes nothing but costs nothing (one-offs); JIT-mono
costs upfront but pays off if repeated. A call site graduates dispatch → JIT-mono when it crosses the
threshold; degrades back to dispatch if it goes megamorphic.

**Why this fits bang UNUSUALLY well.** bang is ALREADY a monomorphizer — `elaborate-to-mono` compiles the
surface to monomorphic KERNEL terms (AOT). So a JIT is not a new mechanism; it is **the same
monomorphization, run LATER**:
```
compile-time-known type  →  AOT-monomorphize → kernel terms   (bite-1/bite-2 today)
runtime-known type        →  JIT-monomorphize → kernel terms   (the same elaboration, triggered at runtime)
```
Two timings of ONE mechanism. Soundness posture is IDENTICAL: monomorphization is the tested-superset
elaboration, and whenever it runs it produces VERIFIED-kernel code (the same differential-tested elaboration
→ the same verified target). The verification rides the monomorphization regardless of WHEN it fires.
CAVEAT: this holds only if the JIT REUSES the verified `mono → kernel → compile` pipeline; an ad-hoc runtime
codegen is instead a TRUSTED component (like the runtime). The tiered dispatch tier is just a dictionary
handler (Q37/ADR-0080).

**Recommended**: static-first (bang today, no change); the dynamic escape is post-v1 (needs existentials
+ a runtime/JIT); when built, TIERED — dispatch cold, JIT-mono hot+stable, megamorphic stays dispatched;
JIT reuses the verified mono→kernel pipeline so it stays inside the soundness story.

**Blocked on**: existentials / `dyn Trait` (Q37 — the feature that CREATES the runtime-known-type case);
a runtime + JIT (post-v1, large); the ◊5 compiled path (WasmFX) as the codegen target. Performance is
second-class in v1 (invariant #7) — this is a post-v1 direction.

**Revisit signal**: existentials are taken up (Q37/ADR-0080's dict-passing trigger) → the Tier-0 dispatch
is the dictionary path; OR a JIT/runtime is built → add Tier-1 JIT-mono with profile-guided graduation; OR
performance becomes first-class (post-v1). Ties [[Q37 FFI as effect]] (existentials = the dynamic case),
[[Q39 what is IO]] (the dynamic/runtime-loaded world), ADR-0080 (dict-passing = the Tier-0 dispatch path),
ADR-0075 (elaborate-to-mono = the shared monomorphization mechanism), the ◊5 compiled path.
