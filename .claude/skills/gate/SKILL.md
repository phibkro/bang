---
name: gate
description: Axiom-gate a Lean headline on COMMITTED content — the cheapest correct answer to "is this proof actually green?". Use at an IC STOP-and-SHOW, before relaying a "green"/"sorry-free" claim, or whenever judging a proof's axiom-cleanliness. Runs force-rebuild + `#print axioms` + the trusted-axiom check on a clean tree; never grep-for-sorry.
---

# /gate — axiom-gate a Lean headline on committed content

The discipline that prevents false-greens (CLAUDE.md "Gate-traps"). A proof is green
iff its axiom set ⊆ `{propext, Classical.choice, Quot.sound}` with **0 `sorryAx`** —
certified by `#print axioms`, **never** by `grep`.

## Usage

`/gate <Fully.Qualified.Theorem> [more theorems…]`

With no args, gate the Audit headlines (`just axioms`).

## Procedure (do exactly this — it is the gate-before-relay contract)

1. **Gate the COMMITTED content, not a summary or a dirty tree.** `git status --short`
   must be clean (or operate on a clean checkout of the sha). If an agent *reported* a
   sha, gate that sha — never its prose. If the tree is dirty with another writer's WIP,
   stop and gate a clean checkout instead.

2. **Force-rebuild the relevant olean** — never trust a stale `.olean`:
   `nix develop -c bash -c 'touch Bang/<Module>.lean && lake build Bang.<Module>'`
   (do NOT `lake exe cache get` in a worktree — #40; `cache unpack` if oleans missing).

3. **`#print axioms` via a `/tmp` scratch file** (no tree pollution):
   ```
   printf 'import Bang.<Module>\nopen Bang.<NS>\n#print axioms <thm>\n…' > /tmp/gate.lean
   nix develop -c bash -c 'lake env lean /tmp/gate.lean 2>&1' | grep -iE "depends on axioms|unknown|error\("
   ```

4. **Classify each headline:**
   - `[propext, Classical.choice, Quot.sound]` (any subset) → **CLEAN**.
   - contains `sorryAx` → **OPEN** — locate the sorry sites (`grep -nE "\bsorry\b"`, mind
     the backtick form), confirm they are the *expected* open seams, not a leak.
   - any other axiom → **FLAGGED** — a real axiom dependency; investigate.

5. **Detect build errors** with the `lake build` exit code or `grep -E "error"` — NEVER
   `grep "error:"` (misses `error(lean.unknownIdentifier):`).

6. **Report** per headline: clean / open(+sites) / flagged, plus the committed sha and
   whether U2/other invariants regressed. That report is what gets relayed — not the
   agent's claim.
