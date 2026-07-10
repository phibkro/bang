<!-- note-status: active -->
# Stranger test — round 1 (2026-07-09)

> The first outer-loop probe: a zero-prior agent, roleplay-strict (README + generated
> reference + examples/ + CLI output ONLY), asked to ship a Caesar-cipher tool from a fresh
> clone. The findings are ground truth about the public docs no internal review can produce.

## Verdict

**8.5/10 ship-ability** — working cipher (encode/decode/round-trip ×3, hand-verified, both
engines byte-identical) on the FIRST conceptual attempt; ~8 min clone→verified program
(build-bound, not learning-bound); zero blockers, two papercuts. **The caveat that matters:
the examples carried the reference** — strip examples/ and the score drops to ~4/10, because
the reference alone does not teach strings.

## The one doc change (the round's headline)

The generated reference's Types/Syntax tables have NO `Str`, NO `Char`, NO string-literal
form. Every string fact the stranger needed (Str = SNil | SCons(Char, Str) · Char(n) is a
codepoint · "..." desugars to the cons chain · match/build idioms · the ASCII contract) was
reverse-engineered from examples/json + examples/tokenizer source. Fix = a Strings &
Characters section IN the generated reference (issue #65). GAP B rides along: the codepoint
encoding is nowhere stated — the stranger GUESSED ASCII from example magic numbers.

## Stumbles + papercuts (issue #66 batches the small ones)

1. `bang --help` exits 1 (should be 0 — a help request is a success; CI smoke-check trap).
2. `intToStr` looks stdlib (used across examples) but is example-LOCAL — nothing marks
   injected-vs-local; the stranger reached for it as stdlib. Fix: mark example-local helpers,
   or the stdlib table gains a "these three only" callout.
3. GAP D (good news shaped as a gap): the multi-arg `! {Div}` machinery inferred everything —
   the stranger braced for a fight that never came. The reference's warning overstates the
   ceremony post-ADR-0091.

## What worked (preserve these properties)

`bang check --json` turned the one real stumble into a 15-second fix (exact span + plain
message) · the README quickstart ran VERBATIM · the reference's ~40 #guard-verified examples
were trusted completely and never burned · `--compiled` ≡ kernel on a real program ·
`bang fmt` clean. The docs' superpower is build-gated examples; the gap is table coverage.

## Method note (repeatable)

Roleplay-strict stranger + forbidden-files list + time-to-first-success metrics + stumbles
quoted verbatim + "one doc change" question. Re-run at each ◊ (the loop-audit's user-loop
row now tracks it). The cipher program: exercised match-on-Str, nested Char(n) match, single+
multi-arg recursion, thunks, sums, arithmetic wrap, concat — a good template task.

**Rebuild-first, always (added after round 2's false-regression scare).** Before scoring
against the binary, REBUILD it from the round's base sha (`nix develop -c lake build bang`,
~2 min warm) — never trust a prebuilt `.lake/build/bin/bang` at face value. Round 2's first
pass hit a stale binary (predating that round's own ergonomics batch) and would have logged
FOUR false regressions (`--help` exit 1, no `--version`, …) that were already fixed on the
base sha — checking the binary's mtime against the relevant commits caught it before the
score was recorded. Same gate-the-clean-sha discipline the proofs use, applied to a CLI
artifact: a stale build is testing a lie, not the code.
