---
type: design-question
title: "Concurrent STM: the privileged shared-heap upgrade"
description: "STM's genuinely-concurrent privileged form (shared heap, opacity) when threads/multi-shot arrive"
status: open
area: effects
ties: ["Q23", "ADR-0030", "ADR-0031"]
see-also: ["references/README.md"]
---
**Question**: how does STM become genuinely *concurrent* (its privileged form) when threads / multi-shot
handlers arrive?

**Why it matters**: ADR-0030 ships v1 STM as a *single-threaded transactional handler* (`state ⊗
exception`); **privilege** — a runtime-owned shared heap that racing transactions validate against — is
exactly what a per-computation handler-fold CANNOT provide, and is load-bearing *only* under concurrency.
The upgrade is the real STM. The all-or-nothing law (`all_or_nothing_abort`, proven) climbs to **opacity**
(Guerraoui–Kapalka) at that point.

**Detail**: needs a shared heap *outside* any handler, optimistic read-set validation, conflict detection,
and `retry`-as-blocking (vs v1's `retry ≈ abort`). Couples to multi-shot handlers (ROADMAP ◊5+) and the
**cooperative-not-preemptive** concurrency model (PRD rung 6). The deferral is sound *only while no effect
observes mid-transaction partial state* (ADR-0030 Revisit-if). Sub-forks already scoped: `orElse` needs a
**recovery handler** even single-threaded (rung-3 follow-on, corrects ADR-0030's "costs nothing");
**general-`S` TVars** via a default-witness (ADR-0030 amendment, deferred to avoid helper churn).

**Options**: (literature in `references/` per ADR-0030) Harris-style log-based optimistic STM with
validation-at-commit; C4-style (Lesani–Chlipala OOPSLA'22) verified transactional objects proving strict
serializability via linearizability — the mechanized exemplar.

**Blocked on**: concurrency / multi-shot (post-v1, ◊5+).

**Revisit signal**: threads / multi-shot land; or a single-threaded program genuinely needs blocking-retry
(which is a concurrency need wearing a single-threaded mask).
