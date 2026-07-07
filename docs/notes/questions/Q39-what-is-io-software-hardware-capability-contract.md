---
type: design-question
title: "What is IO? — the software↔hardware capability contract as a family of typed effects"
description: "IO is not a primitive but the family of program↔world effects; each is a typed interface + handler; the software↔hardware contract IS the effect interface; the net interface first (web-server-demanded); HKT makes contracts implementation-agnostic + lawful"
status: open
area: effects
ties: ["Q37", "Q30", "Q33", "ADR-0030", "ADR-0075"]
see-also: ["the web server / client (docs/roadmap/project-roadmap.md)", "Zig's Io interface", "bite-3 HKT (PATH-polymorphism)", "Go net/http"]
---

**Question**: what IS "IO"? It feels like an impossibly broad category — input/output to the external
world. The resolution in bang's frame: **IO is not a primitive; it is the UNION of every EFFECT that
crosses the program's boundary to something it does not control**, each a typed INTERFACE realized by a
HANDLER. So the design question is (a) how to DECOMPOSE IO into a family of typed effects, and (b) how HKT
makes those interfaces implementation-agnostic + lawful.

**Why it matters**: most languages treat IO as one primitive (a `print`, a syscall layer) — which is why it
feels unbounded. bang already decided otherwise (kernel is pure; the world enters as effect+handler,
invariant #5). Naming the decomposition + the contract explicitly turns "IO" from a vague category into a
principled family — and it's the foundation for the OS/distributed northstar.

**The framing — the software↔hardware (↔world) contract IS the effect interface:**
```
software's DEPENDENCIES on the world  =  its effect ROW        (its capability manifest — Q37)
the world's EXPOSED CAPABILITIES       =  the available HANDLERS
the CONTRACT between them              =  the effect INTERFACE  (ops + types + LAWS)
the OS                                 =  the layer that MULTIPLEXES hardware into handlers
```
An OS is not special in this frame — it is a big handler installation over hardware effects. "What does
software ask of hardware, and how does hardware expose it" is answered once: effects are the ask, handlers
are the exposure.

**The taxonomy (decompose IO into effects; grow demand-driven):**
```
memory            {Alloc}/{Memory}      mostly a runtime handler in a high-level lang; QTT/grades account it (Q30/Q33)
cores / threads   {Scheduler}/{Spawn}   concurrency — over STM (the privileged primitive, ADR-0030)
IO devices        {Net} · {FileSystem} · {Graphics} · {Input}   each a driver bridged by a handler
clock / entropy   {Clock} · {Random}    environment
```

**The NET interface — the FIRST concrete instantiation (operator-requested), stretched by the web server/
client project.** A `{Net}` effect (`listen`/`accept`/`read`/`write`) realized by a handler over the FFI
seam to the OS network stack (the Q37 mechanism). BETTER than Go's `net/http` (a plain function library):
capability-secured (no `{Net}` handler in scope ⟹ the code CANNOT network — least-privilege by
construction), effect-tracked (the row shows a fn touches the net), swappable handler (mock-net for tests ·
real-net for prod → testable IO for free). The web server/client is the DEMANDING project (the stress-test
ratchet: it stretches → the kink is "no IO" → the net-effect + concurrency get driven into existence, like
the tokenizer demanded polymorphism).

**Zig's `Io` interface validates the model.** Zig's new `Io` is dependency-injection for the CONCURRENCY
strategy (pass an IO impl as a value → the same code runs blocking / green-threaded / async). That is
EXACTLY bang's "a handler is a value installed at the use site" — discovered independently for one axis.
bang's is the same move, TYPED + capability-secured + LAWFUL (the handler is a checked interface the row
tracks, not just an injected struct).

**HKT makes the contract IMPLEMENTATION-AGNOSTIC + lawful (why HKT stays on the roadmap, bite-3).** HKT
(`Monad m`, `Functor f`, or a trait OVER an effect) lets code be written against the INTERFACE, not any
handler — and the LAWS make "satisfies the contract" checkable (differential-test a handler against the
laws). That is the lawful-generic form of Zig's `Io` interface: an implementation-agnostic contract you
swap real/mock/remote handlers under, WITH the laws as the acceptance test for a valid handler. It upgrades
an effect from "a plugin point" to "a SPECIFICATION with a conformance test."

**Recommended**: the **net interface FIRST** (the web server demands it; the Q37 FFI-as-effect mechanism);
the broader taxonomy grows DEMAND-DRIVEN (each device-effect when a project needs it — the stress-test
method); the HKT-for-agnostic-interfaces layer rides **bite-3** (HKT) when a project wants handler-agnostic
+ law-conformant IO.

**Blocked on**: Q37 (the FFI-as-effect seam mechanism — the net handler needs it); a real runtime/IO story
(post-v1); bite-3 (HKT) for the agnostic-interface layer.

**Revisit signal**: the web server / client project is taken up (build the `{Net}` effect + FFI handler);
OR concurrency is taken up (the `{Scheduler}` effect over STM); OR HKT lands (make effect interfaces
handler-agnostic + law-conformant). Ties [[Q37 FFI as effect]] (the seam MECHANISM; this is WHAT crosses
it), [[Q30 FBIP]] + [[Q33 memory model]] (the memory/resource effect), ADR-0030 (STM/concurrency = the
scheduler substrate), ADR-0075 (bite-3 HKT — the agnostic-interface layer), the project-roadmap (web
server = the demanding project).
