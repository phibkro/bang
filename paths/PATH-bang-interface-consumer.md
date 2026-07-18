# PATH-bang-interface-consumer — make BANG consume its compiler fact graph once

> Prove the toolchain can be built from BANG programs by reading two live compiler dumps through
> ordinary language libraries and host effects, while retaining the canonical Python consumer as oracle.

## Seam

- **From checkpoint**: the compiler exposes law-aware module interfaces and `interface-diff.py`
  consumes them honestly, but every compiler-fact consumer is written in Python.
- **To checkpoint**: a BANG program reads two live dump lines, parses `moduleInterfaces`, and reports
  preserved/moved/added/removed modules byte-for-byte with the canonical consumer on shared fixtures.
- **Contract preserved**: this is a dogfood witness, not a replacement build tool, cache decision,
  fanout calculation, law-attribution engine, or reusable artifact.

## Layer

- [ ] Kernel  [ ] Compiler  [x] Surface/library program  [x] Meta (harness/docs)

## Actor journey / observable outcome

- **Actor / need**: a BANG tool author wants to consume the same immutable compiler facts external
  tools already use, without inventing a second checker or privileged runtime.
- **Public starting point**: generate two `bang query dump <entry.bang>` lines and pipe them to
  `bang run --env=real --allow=Console examples/json/interface-moved.bang`.
- **Terminal observation**: the program prints one ordered `preserved|moved|added|removed <module>`
  line per module; the harness derives the expected lines from `tools/interface-diff.py`.
- **Adverse / recovery route**: malformed JSON, a missing/wrong `moduleInterfaces` field, an invalid
  row, or a duplicate module identity yields the single line `invalid dump`, never a partial verdict.
- **Downstream journey released**: BANG has one real compiler-fact consumer; the next toolchain step
  may return to the independently lowerable module identity/body/link seam with a concrete consumer
  already waiting above it.

## Feeds the constraint

- **Binding constraint now**: the project roadmap defines the toolchain rung as “BANG tools consume
  the compiler fact graph,” but no BANG program previously did so.
- **How this path feeds it**: reuse the shipped JSON module, resolver, Console effect, query dump, and
  canonical consumer in one end-to-end journey; compiler/kernel changes are prohibited by scope.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| the JSON showcase cannot parse real compiler output | pre-scope live dump probe | realized / high / low | **recognize empty close only at container entry; refuse trailing commas; gate a fresh dump** | another real dump field fails |
| dump-sized lines exceed the host/string path | 6,249-byte live payload, measured ~0.54s for ingest probe | low / high / medium | **retain live generated-input gate; make no performance claim** | representative input times out or crosses a budget |
| a partial parse is mistaken for a dump | `parseTop` deliberately ignores trailing input | high / high / low | **add `parseComplete`; require empty remainder** | any consumer uses `parseTop` for protocol input |
| malformed structure yields a plausible empty result | missing arrays/rows can resemble zero modules | high / high / medium | **validate field kind, nonempty module/digest, list shape, and uniqueness; one refusal** | malformed input emits a status line |
| an empty result leaks a runtime representation | synthetic empty interface sets rendered `fold inl ()` instead of protocol rows | realized / medium / low | **require the current producer invariant: at least `@entry`; refuse empty arrays** | dump producer permits zero modules |
| dogfood witness is mistaken for canonical build logic | Python consumer validates topology, algorithms, exports, and law attribution | high / critical / high | **differential oracle; document witness-only scope; Python remains canonical** | docs recommend replacing `interface-diff.py` |
| digest-only comparison launders a producer inconsistency | BANG view does not recheck digest/export agreement | medium / critical / medium | **accept only live producer dumps in the positive claim; no authorization/skip result** | BANG output is used as cache authority |
| recursive parser permits resource exhaustion | unbounded line input and cons-list strings | medium / medium / medium | **example/tool witness only; measured fixture, no availability claim** | exposed as a long-running service or untrusted-input tool |
| host access widens beyond need | Console already supplies line input | low / high / low | **grant only Console; no filesystem/network surface** | consumer needs persistent files or remote facts |
| library repair expands without bound | first live input could reveal a cascade | medium / medium / medium | **stop after two additional leaf defects or any compiler change** | third independent parser defect appears |
| output claims fanout, checking, or reuse | program reports interface status only | high / critical / high | **exclude topology closure, law attribution, exit semantics, skips, cache, and speedups** | an independently validated artifact exists |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: Python or eyeballing was required to answer whether a module
  interface moved; BANG had never consumed a compiler fact. The first 6,249-byte live dump reached
  `Console.readLine` intact but parsed as `None`.
- **First yield**: `[]` and `{}` returned their `JNilL` payload while leaving the closing delimiter
  in the remainder. Parent containers refused, so `{\"x\":[]}` and the live dump were red.
- **Smallest repair**: consume an immediate `]`/`}` only at container entry and add a strict
  `parseComplete` projection. Skeptical review caught that recognizing close inside the recursive
  tail also admitted `[1,]`/`{\"a\":1,}`; refusal poles now preserve strict JSON. No
  parser/compiler surface or kernel code changes.
- **Smallest tracer bullet**: `query-dump.bang` proves one fresh dump parses completely as a JSON
  object; `interface-moved.bang` then compares two interface row sets.
- **Strongest falsifier**: BANG status lines diverge from `interface-diff.py` for the same moved,
  added, or removed fixtures, or malformed input produces any partial status line.
- **Assumptions / exclusions**: input is a current `bang query dump` producer line. Synthetic empty
  `moduleInterfaces` sets are refused because current dumps always contain `@entry` and an empty
  rendered string leaks a non-protocol runtime representation; a missing second line is likewise
  refused as `invalid dump`. The witness does
  not validate dump/interface schema versions, scopes, algorithms, export/digest agreement, dependency
  topology, law movement, semantic equality, fanout, actual work, artifact reuse, exit codes, latency,
  availability, or replacement of the canonical consumer.

## Plan

1. [x] Have the persistent advisor rank the next tracer and run dump-size/Console/JSON kill shots.
2. [x] Pin and repair the bounded empty-array/object defect; add complete-input parsing.
3. [x] Implement the BANG interface-status view and differential moved/added/removed journeys.
4. [x] Regenerate governed views, obtain skeptical review, run exact-tree convergence, and publish.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Focused evidence: `tools/test-query.sh` — **249 passed, 0 failed** with Python + jq available,
  including trailing-comma, empty-interface, and EOF refusal poles.
- Engine parity: kernel oracle and compiled machine both report `json → 30163`; both full example
  journeys pass **61/61**.
- Skeptical review: **no remaining blockers** after correction; digest-level trust, current-producer
  nonempty input, EOF behavior, and the named topology/authority exclusions remain limitations rather
  than hidden claims.
- Project fitness: **PASS** against explicit stable parent `7b68e928`; the predecessor's virtual
  changelog identity was normalized to its canonical history identity.
- Convergence evidence: exact-tree `just verify` passed the **1452-job** Lean build, both **61/61**
  example engines, **31/31** batteries, the live 33-theorem axiom audit, all architecture/proof
  falsification poles, and the full fitness bundle.
- Retained stop condition: a third independent JSON leaf defect, any required compiler/surface change,
  strict-input regression, or failure to match the canonical consumer stops and splits a hardening unit.
- Reopen / observe: a larger real dump exceeds practical fuel/time; an untrusted-input deployment needs
  explicit resource limits; or a BANG consumer needs validated fanout/artifact authority.

## Owner

- Agent / human: Codex, with persistent read-only Fable 5 strategic advisor in Herdr
