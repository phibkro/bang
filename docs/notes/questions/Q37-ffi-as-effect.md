---
type: design-question
title: "FFI as a typed EFFECT: the external-boundary seam (schema-declared contract · capability security · the road to OS/distributed)"
description: "northstar direction — the first interactive-program capability"
status: open
area: effects
ties: ["Q36", "Q33", "Q38", "ADR-0026", "ADR-0030"]
see-also: ["#44", "#48", "docs/roadmap/bang-northstar-roadmap.md"]
---
**Question**: how does bang reach the OUTSIDE WORLD (IO · graphics · network · syscalls · other nodes)?
The seam: FFI-as-a-typed-EFFECT — an external boundary is an effect whose handler lives on the other side.
How is the CONTRACT at that boundary declared, trusted, and checked?

**Why it matters**: bang's kernel is PURE (no IO primitive); the outside world MUST enter as an EFFECT
(invariant #5 — a handler + runtime host-imports, NOT a sixth primitive). This is the first INTERACTIVE-
program capability (games, tools, servers) AND the boundary mechanism for the set northstar (OS /
distributed systems — a syscall is an effect · a driver is a handler · the network is an effect · an
inter-node RPC is a cross-node effect seam). North stars are ambitious; this one stress-tests the whole
system. NB the effect seam is the UNIFYING external boundary — not a graphics question, THE moat question.

**Two architectures (pragmatic bridge vs on-thesis vision):**
- **(B) bang as a verified BACKEND, called via wasm/FFI** — a host (C/Rust/Zig + raylib, or any embedder)
  drives; bang exposes PURE functions (`step : Grid×Move → Grid`). PRAGMATIC + instantly useful; sidesteps
  IO-effects + #48. BUT relinquishes the bang type system ACROSS the seam (host is outside bang's
  guarantees; the entry point must re-validate untrusted input — parse-don't-validate). Typed island in an
  untyped sea.
- **(A) bang FFI through EFFECTS** — bang drives; external ops are effect operations (`draw : Scene → ()
  ! {Raylib}`), the handler is the external seam. MORE ambitious (needs the FFI-as-effect mechanism +
  effectful recursion #48 + a runtime with host-imports) ⟹ MORE northstar-worthy. On-thesis: "a program's
  runtime is a handler installed at the use site" — the external runtime is just a handler.

**The seam contract (the fork — operator's instinct):** NOT a raw C ABI (implicit memory layout, brittle,
hand-matched) but a DECLARED contract in a standardized schema — RPC/network-protocol-shaped
(protobuf/gRPC · Cap'n Proto · JSON-RPC · OpenAPI lineage). The wasm-native answer, and bang targets
WasmFX: **WIT / the WebAssembly Component Model** — one declarative interface file, guest + host both
GENERATE bindings from it. KEY ALIGNMENT: **an effect's operation signatures ARE the schema** — a
`{Raylib}` effect declaring `drawRect : Rect → ()` IS the interface contract; the effect ROW tracks WHICH
contracts a program depends on; the handler binds contract → implementation (trusted-external OR
pure-mock). bang's effect system already has the shape of an RPC interface declaration; the FFI just means
the handler is external. No bolt-on schema language needed — the effect IS the IDL.

**The contract is TWO layers — schema (shapes) AND laws (behavior):** schema-validation checks TYPES
(structural, by construction — WIT-style); but bang has traits+LAWS (ADR-0068), so an effect can declare
LAWS between its operations (`pop(push(s,x)) = (s,x)`), and those laws become a PROPERTY-TEST ORACLE for
the trusted external handler — generate op sequences, run them through the real handler, assert the laws;
spec-vs-implementation drift at the seam becomes FINDABLE. This is "proof rides the reference" aimed at the
EDGE: the external module is UNVERIFIED (trusted code), but its BEHAVIOUR is law-checked. The strongest
form of the seam — not "I trust you" but "I trust your code AND I'll test that you obey the contract you
declared." The laws turn an effect from an interface into a SPECIFICATION. (Ties [[Q38 module ≟ effect]] —
the laws live on the shared interface, whichever construct it is.)

**Trust (steer on "assumed trusted" — split by seam type; an unchecked contract is a C ABI with docs):**
trust the external IMPLEMENTATION (unverified C/host/remote code), but for the DATA — in-process
schema-GENERATED bindings agree BY CONSTRUCTION (shapes match, no per-call check, like protobuf codecs);
untrusted/NETWORK seams VALIDATE at ingress (parse-don't-validate — turn untrusted bytes into typed values
so illegal cross-seam states are unrepresentable INSIDE bang). "Trust the code, validate the bytes across
an untrusted seam" — SOUL's "receiver guesses nothing" applied to the wire.

**THE PAYOFF — capability security (why this is northstar-DEFINING):** a handler is installed at the USE
SITE, so a program can only perform an effect it's been HANDED. A program's effect ROW = its CAPABILITY
MANIFEST (which external resources it may touch); no `{Net}` handler in scope ⟹ it CANNOT do network —
least-privilege BY CONSTRUCTION. Sandboxing · driver isolation · per-process capabilities all fall out of
"effects are values you hand out" (unlike C, where any code calls any syscall). The FFI-as-effect isn't
just an IO model — it's the SECURITY ARCHITECTURE of the whole system. The foundation for the OS/distributed
moat.

**Stratification placement:** the external program runs on the COMPILED path (WasmFX + host-imports), NOT
`Source.eval` (pure — can't do real IO). LOGIC stays verified/tested core (pure, `#guard`ed vs
`Source.eval`); the IO seam is the trusted/tested edge; the effect row IS the marked seam (ADR-0026,
language-level). Verified core · trusted edge · marked boundary — the stratification, one level out.

**Recommended**: (B) FIRST as the instantly-useful bridge (embed pure bang, host owns the loop+IO — proves
the compiled artifact + gets an interactive demo without #48/IO-effects). (A) as the northstar (FFI-as-
effect + WIT-style contracts + capability handlers). Both share the schema-contract; start with WIT since
bang already targets wasm.

**Blocked on**: a real IO/runtime story (post-v1); polymorphism (richer external data); #48 (effectful
recursion, for a bang-DRIVEN loop). A KEYFRAME, not a near-term increment.

**Revisit signal**: an interactive demo is wanted (do B); OR the OS/distributed northstar is taken up (A +
capability handlers + the contract schema); OR the WasmFX backend gains host-imports. Ties the northstar
roadmap (`docs/roadmap/bang-northstar-roadmap.md`), **#44** (user-defined effects — the effect-declaration
surface the contract needs), **#48** (effectful recursion), ADR-0026 (stratification = the trust seam),
ADR-0030 (STM/concurrency — the distributed substrate), [[Q36 gradual correctness]] (untrusted-boundary
validation = a runtime-check hatch), [[Q33 memory model]] (data crossing the seam — copies vs shared).
