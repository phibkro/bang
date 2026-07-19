---
type: design-question
title: "Proof export: laws fuzzed by default, PROVABLE on demand (#prove → a Lean goal over the elaborated term)"
description: "the stratification seam surfaced into user programs — one law construct, two rigor rungs; content-addressed proof cache"
status: open
area: tooling
ties: ["Q34", "ADR-0068", "ADR-0076", "ADR-0093"]
see-also: ["docs/notes/verification-ladder.md", "#39", "#60"]
---
**Question**: should a bang `law` be exportable as a PROOF OBLIGATION — a `#prove` pragma that
turns the law's statement into a Lean goal about the program's ELABORATED kernel term,
discharged in the host (by an agent or human), cached content-addressed?

**Why it matters**: this is the genuinely novel verification rung available to bang
specifically — programs already elaborate into a Lean kernel carrying a verified semantics
(`Source.eval` + the trusted-three census), so types-as-propositions does NOT require making
bang a proof assistant. The same `law` declaration is **fuzzed by default (#60), provable on
demand** — one construct, two rigor levels, an explicit seam. The stratification principle
(verified core / tested superset) surfaced into user programs: "your paradigm is your row;
your rigor is your rung." Full context + the evaluated-and-set-aside HoTT question:
`docs/notes/verification-ladder.md` (operator hypothesis 2026-07-09).

**The shape (sketch, not decided)**:
- `#prove lawName` marks a law for export; `bang prove` (or the queryable-compiler service,
  ADR-0076 #2) emits the Lean goal: the law's equation over `Source.eval` of the elaborated
  terms, universally quantified over the sampled variables' types.
- The discharged proof is cached by the CONTENT HASH of the elaborated term + the goal
  (ADR-0076's Merkle machinery) — a proof is valid exactly until the term's hash changes;
  a stale proof is UNREPRESENTABLE, the same by-construction move as the incremental build.
- Un-discharged `#prove` = a named, visible debt (the proof-state block pattern), never a
  silent pass — the law still fuzzes meanwhile.

**The mechanics (operator discussion 2026-07-09) — why bang gets this nearly for free**: the
elaborated program IS a Lean value (the kernel AST is a Lean inductive), and the evaluator that
runs it (`Source.eval`) is the same function the theorem quantifies over — no encoding gap, no
second semantics; the oracle and the proof subject are one construct. `bang prove --emit`
writes a `.lean` artifact: the elaborated terms quoted verbatim + the goal
(`∀ args, WT → ∃ v, Evals lhs v ∧ Evals rhs v`) + `sorry`; a prover (agent or human)
discharges it with the whole spine's lemma library in scope; the cache keys on
hash(terms + goal). Statement form follows the ROW: total fragment (⊥, structOK-certified) →
clean value equality (termination provable); Div fragment → partial correctness / up-to-fuel;
the ◊4 binary LR (contextual equivalence) is the eventual gold-standard relation. Lifecycle is
fail-loud in every state: undischarged = named visible debt (still fuzzing), discharged =
cached, edited = hash-miss = reopened red automatically.

**Forks to settle at design time**: goal shape (over `Source.eval` at fuel — how is the fuel
quantified? partiality via the Div seam?); where proofs LIVE (in-repo .lean files keyed by
hash? a proofs/ dir?); what fragment is exportable v1 (⊥-row total fragment first — the
fuel question vanishes there); how the obligation names bang-level variables readably
(agent-first: the goal should be readable by the prover-agent).

**Vocabulary input (2026-07-19)**: keep the boundary proof-relevant on the export side and
proof-irrelevant on the trusted-language side. Exported law evidence is **proof-relevant**: a concrete,
content-addressed Lean term whose identity and validity travel with the obligation. The BANG TCB's
internal truth boundary remains proposition-valued / proof-irrelevant; proof artifacts are checked by
the existing Lean boundary and do not become new trusted language mechanisms. No proof term enters or
widens the BANG TCB. This names the intended fork; it does not decide the artifact format.

**Blocked on**: ADR-0093 modules (laws from imports), #60 (`bang test` — the default rung the
export escalates FROM), and practically the ◊-schedule (post-#44-arc).

**Revisit signal**: #60 ships and a user (or the stdlib) wants a law's rigor upgraded past
sampling; OR the ADR-0076 content-addressed build lands (the cache machinery becomes real).
