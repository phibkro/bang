---
type: design-question
title: "Undecidable + unsafe programs: effects-with-oracles vs FFI"
description: "admit non-terminating (Div) + unsafe programs as row-tracked effects with oracles, not FFI holes"
status: open
area: effects
ties: ["Q37", "ADR-0026"]
see-also: []
---
**Question**: how does bang admit programs that (a) may not terminate ("undecidable") or (b) leave the
verified abstraction ("unsafe": raw memory, MMIO, type holes, foreign code)? Write them in the
language, or port them over FFI?

**Why it matters**: the xv6 golden test (PRD §3.1) NEEDS both — a scheduler loop runs forever, device
drivers poke MMIO. If these are FFI escape hatches, invariant #1 ("never ship an execution path with
no oracle") is violated at exactly the places correctness matters most. The answer shapes whether
`Div`/`Foreign` effects and coinduction enter the kernel.

**Detail (the on-thesis direction — proposed, NOT built)**: both axes become **effects in the row**,
contained by handlers, each backed by an oracle — generalizing STM (invariant #3: one privileged,
axiom-backed primitive):
- **Undecidability = partiality as the `Div` effect** (Capretta's `Delay` monad; McBride,
  *Turing-Completeness Totally Free*, 2015). `⊥`-row = total (provable, foldable); `Div`-row = may
  diverge (only runnable). bang ALREADY embodies this: `Source.eval : Nat → Comp → Result Val` — fuel
  is the partiality handler, `oom` the honest timeout. Rice/Halting forces the total-vs-partial
  tiering (can't have Turing-completeness + a total static termination check). Third tier: *productive*
  non-termination (the xv6 event loop) = **coinduction**, which is the reactive model (rung 4).
- **Unsafety = a privileged op named by an effect, backed by a differential-test oracle.**
  unsafe-but-modelable (MMIO, syscalls) → a `Mem`/`IO` privileged primitive tested against the real
  hardware/model (NOT proven — invariant #1's boundary discipline). Genuinely foreign code → a
  `Foreign` effect; the artifact is its own oracle.
- The **effect row is the firewall**: pure code cannot silently call a diverging/unsafe op — the tag
  propagates into the type, so contamination is visible and type-enforced.

**Decision rule (proposed)**: write it in bang if you can give it an oracle (a proof, or a model to
differential-test); FFI only when the foreign artifact IS its own best oracle and re-verifying isn't
worth it — and name what FFI gives up (the proof stops at the boundary; downstream is `Foreign`-
tainted). For the xv6 showcase, lean write-it-all-in-bang (seL4 / CertiKOS precedent — CertiKOS has
only a tiny verified-asm layer); FFI is for real-world pragmatics (don't re-verify OpenSSL), not the
golden test.

**Options**: (1) effects-with-oracles as above — `Div` + coinduction for partiality, privileged
primitives + `Foreign` for unsafety, all row-tracked *(recommended; on-thesis)*; (2) a two-world
split (a separate "unsafe bang" dialect outside the verified core) — rejected unless (1) proves
unworkable, as it abandons the firewall; (3) FFI-only for everything non-total — rejected (blind spot
at the highest-stakes code).

**Blocked on**: nothing now — this is ◊4/◊5/post-v1 (needs the compiler + a richer effect zoo). Far
ahead of rung 1.

**Revisit signal**: a program on the ladder needs non-termination (the scheduler, rung 6) or a raw/
MMIO op (the device driver, rung 8); or the effect-zoo design for v1+ effects begins.
