# 0044 — Dynamic vs lexical handler dispatch (v1 stays dynamic; named handlers a recorded future)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: v1 keeps DYNAMIC handler dispatch (`splitAt` outward search; ADR-0023/0024). Lexical/named handlers (capability-targeted, à la Koka named handlers / Lexa tunneling) are NOT adopted but recorded as a future direction: they would dissolve the ADR-0043 resume-through-a-wrap edge and turn the verification seam into a per-handler USER CHOICE — at the cost of a second dispatch path whose library-encodability (vs a 6th primitive) is unverified.
- **Depends-on**: 0043, 0024, 0023, 0016, 0001

## Context

Our kernel dispatches effects **dynamically**. A perform `up ℓ op v` (Syntax.lean:158) carries a **static**
label `ℓ`; `splitAt K ℓ op` (Operational.lean:255) walks the runtime stack **outward** for the nearest
handler discharging `ℓ`, and its recursive branch (`:259`, `else (splitAt K).map (prepend handleF h)`) walks
**past non-catching handlers**. That "walk past a non-catching handler" is *exactly* the configuration that
produces the ADR-0043 resume-through-a-wrap edge (the one tested-descent corner of `lr_sound`). Which handler
catches a given op is a function of the **runtime** call context.

**Lexical dispatch** (Lexa/tunneling — Ma OOPSLA'24, Zhang POPL'19; Koka *named handlers*; Effekt capabilities)
resolves op→handler by **static scope** instead: a handler installation yields a fresh **capability**, and a
perform targets that capability **directly**. Which handler catches is fixed lexically, not by ambient search.
The wrap-skip search never happens, so the ADR-0043 edge does not arise, and accidental handling is
structurally impossible.

This is a genuine **language-design fork**, not a proof detail. We chose dynamic in ADR-0023/0024.

## Decision

**v1 keeps DYNAMIC dispatch.** Rationale:
1. It is the **canonical** algebraic-effects semantics (Eff, OCaml 5, Koka's default) — familiarity + interop.
2. The **calculated VM** (ADR-0016, invariant #4) is derived *over* the `splitAt`-search dispatch; changing
   dispatch re-runs the Bahr–Hutton calculation **and** the LR. The ADR-0043 literature sweep priced a switch
   to lexical at ≈ the declined typed-relation reshape (it threads the calculated machine + an ADR reversal).
3. We **already** have lexical's headline guarantee: `no_accidental_handling` proved **0-axiom** (ADR-0024) via
   lacks-constraints — the structural analogue of Zhang's tunneling. So dynamic + our lacks-discipline already
   captures the safety property; the *only* things pure-lexical adds are (a) dissolving the one tested edge and
   (b) making that safety **structural** rather than **proved**. Small marginal gain for a different language.

Lexical/named handlers are **not adopted in v1**, but the "support both" direction is recorded below because it
is the most principled future move and changes the seam from a hard limit into an opt-out.

## Could we support BOTH? — design analysis

**Precedent:** yes, coexistence is established, not novel. **Koka** ships both regular (dynamic) and **named**
(lexical) handlers in one language; **Effekt** is capability-based throughout. So "both" is a known point in
the design space.

**On-brand framing:** per the project thesis ("paradigm and runtime are *values*, not language features"),
dispatch *discipline* should be a **library-level choice over the kernel** wherever possible — not two kernel
mechanisms. The question is how far that reaches.

### Machinery — two options, and the sharp line between them

- **Option A — lexical SCOPING (cheap, ~library-level, does NOT dissolve the edge).** Add fresh-label
  generation (a `fresh`/gensym capability — plausibly library-encodable via a counter/state handler, or a small
  kernel affordance). A `named h` combinator installs `h` at a **fresh unique label** `ℓ_fresh` and returns the
  capability `c = ℓ_fresh`; `perform[c] op v` is just `up ℓ_fresh op v` through the **same `splitAt`**. This buys
  lexical **scoping** — the capability uniquely names the handler, so no other handler can shadow it (no
  accidental handling for `c`). It does **not** dissolve the ADR-0043 edge: `splitAt` still walks past
  intervening handlers *for other effects* (`:259`), so the wrap configuration + the answer-type-recovery
  obligation persist. Kernel stays at **5 primitives**.
- **Option B — edge DISSOLUTION (real machinery change).** Named handlers use **direct** dispatch: the
  capability transfers control to the handler **without** the outward walk (true tunneling, Lexa-style). This is
  what makes the wrap-MISS *unrepresentable* and the resume case fully verifiable. Cost: a **second dispatch
  path** alongside `splitAt`; whether it is **library-encodable** over the kernel (preserving invariant #5's
  five primitives) is **unverified** — it may be a 6th-primitive-class change requiring its own ADR + spike, and
  the calculated VM would need a dispatch arm for it. The ADR-0043 sweep found Lexa's direct dispatch threads the
  calculated machine — evidence Option B is non-trivial.

The honest gap: **Option A is cheap but buys no verification win; Option B buys the win but its cost
(library-encodable vs new primitive) is the open question.**

### User experience

```
DYNAMIC (today)                          NAMED / LEXICAL (proposed)
─────────────────────────────────────────────────────────────────────────────
with h handle {                          with h as c handle {        -- binds capability c
  … perform op v …    -- ambient search    … perform[c] op v …       -- targets c directly
}                                        }
concise; relies on the runtime stack;    explicit; no accidental handling by construction;
accidental handling proved-absent (0024) (Option B) the resume-edge is VERIFIED, not tested
```

**The payoff:** supporting both turns dispatch discipline **and the verification seam into a user knob.** The
default `with h` stays concise + ambient, carrying the ADR-0043 tested seam on the wrap-edge. Opt-in `with h as c`
is explicit, structurally safe, and (Option B) **fully verified** — so a user who needs the wrap-edge *proved*
for a particular effect simply uses a **named handler** for it. That is maximally on-brand: the discipline
becomes a *value the user selects*, not a fixed language feature, and the one tested corner becomes opt-out
rather than a hard boundary.

## Rejected alternatives (for v1)

- **Pure-lexical (replace dynamic).** A different language: overturns ADR-0023/0024, re-runs the calculation +
  the LR, and trades canonical-effects familiarity for a guarantee (no accidental handling) we **already prove**
  0-axiom. Poor ROI now.
- **Adopt named handlers in v1.** Surface + machinery cost before v1's core ships, and the verification win
  (Option B) is unproven-encodable. Defer to a spike.

## Consequences

- v1 ships **dynamic dispatch**; the ADR-0043 tested seam stands as the verified-final boundary for that design.
- **Recorded future spike** (bounded, mirrors the typed-CrelK probe): (1) Is `named`/fresh-label **Option A**
  library-encodable while keeping 5 primitives? (2) Is **Option B** (direct dispatch) library-encodable, or a
  6th primitive? (3) Does Option B actually **dissolve the ADR-0043 edge** end-to-end (a bounded LR probe)? If
  all three land, named handlers become the **"opt-in to full verification"** mechanism — a strong product story
  in which the language is safe-by-default (dynamic + proved-no-accidental-handling) and *provably-complete on
  demand* (named + edge dissolved).
