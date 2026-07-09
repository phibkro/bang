# ADR-0088 · #48 effectful recursion: row-carrying recursive thunk type, row DECLARED not inferred

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: A `let rec` body currently cannot carry ANY latent effect — the μ-encoded knot's type `recTy = μX. Thunk(X → T)` forces the recursive thunk PURE (`tThunk` ⟹ ⊥), so the #45 fold-payload check (`φ' ⊆ φ`, φ=⊥) REJECTS a body that `raise`s, touches state, or calls a Div helper (#48; found in #47's soundness audit, case ⑤). This is sound-by-rejection but a T1-ergonomics completeness gap: a recursive parser that performs, or a recursive fold calling a partial helper, cannot be written. **Decision: implement #46 Option B as a row-carrying recursive thunk type — `recTy = μX. Thunk_ρ(X → T ! ρ)` — with ρ DECLARED in the `let rec` type annotation (`let rec f : Int -> Int ! {throws} = …`), never inferred by fixpoint.** The body checks against declared ρ (`φ_body ⊆ ρ` — the #45 arm generalizes from φ=⊥ to φ=ρ); inner self-calls type at ρ (retiring Option A's inner-⊥ under-approximation); the effective knot row stays `ρ ∪ (structOK ? ∅ : {Div})` so #47's termination certification keeps eliminating Div orthogonally. Elaborator-only (elaborate-to-mono, ADR-0075 pattern): the kernel, census, and frozen statements are untouched. **Rejected**: fixpoint row inference (implicit where explicit is available — violates the agent-first lens and the config-explicit-at-boundaries principle; more machinery for a worse contract), and effect-polymorphic recursion (needs #56's full Rémy treatment; nothing v1 writes requires it).
- **Depends-on**: 0073, 0074-adjacent (#45 fold-payload check), 0019, 0020, 0075
- **Relates-to**: #48 (the gap), #46/#47 (the landed Div-row + structOK seams this composes with), #56 (single-ρ subeffecting — the `φ_body ⊆ ρ` premise IS one subeffecting site; whatever #56 decides inherits it), OPEN_QUESTIONS (⊥-row⟹terminates soundness — D4)

## Status

Proposed (2026-07-09, drafted while the str49/repl7/out54 lanes run) — awaiting operator ruling.
Implementation is **entry-gated on the str49 lane landing** (#49/#50): both touch the same
`TypeCheck.lean` regions (one writer per file).

- **Layer:** F (frontend/elaborator only — `recTy` construction, the #45 fold-payload arm, the
  `let rec` annotation grammar). No kernel constructor, no frozen statement, no census motion
  possible: the row lives in `IVTy`/`ICTy` at elaboration and erases to the same mono kernel
  terms (`Div` already erases at lowering; other labels elaborate exactly as they do for
  non-recursive functions today).

## Context

**What landed already (the seams this composes with):**
- ADR-0073 §1: `let rec` runs (μ-encoded knot, fuel-bounded runtime).
- #46 **Option A** (closed 2026-07-05): `Div` rides the OUTER knot via `.divMark`
  (`TypeCheck.lean:1729` — `f : Thunk ! {Div} T` at the call site), inner self-calls typed
  pure ⊥ — explicitly documented as a v1 under-approximation. `letRecRow` is the seam.
- #47: `structOK` certifies single-arg structural recursion → removes `Div` from the knot row.

**The wall (#48, verified):** the knot's recursive TYPE is pure by construction. `checkProg`
rejects a `let rec` body with any latent effect ("thunk body effect exceeds the declared
bound") — general, not Div-specific (a `raise`-ing body reproduces it). Root cause is the
type, not the check: `μX. Thunk(X → T)` has nowhere to put a row, so the #45 fold-payload
check is CORRECT to reject — the fix is to give the type a row slot, not to weaken the check.

**Agent-first lens (operator ruling 2026-07-09):** concise EXPLICIT context over implicit
inference; ride existing conventions. `let rec` already REQUIRES a type annotation — the row
belongs in it, in the same `! {…}` syntax every other bang signature uses. A declared row is
the contract an agent can read in one line; a fixpoint-inferred row is invisible until an
error surfaces it.

## Decision

### D1 — row slot in the recursive thunk type

`recTy = μX. Thunk_ρ(X → T ! ρ)` — the row sits where every other bang row sits: on the
`U`/thunk (graded-CBPV `U_ρ`, ADR-0019/0020 "effects ride the U/judgment"), mirrored in the
codomain result row so force+apply propagate it to callers unchanged. This is the same
placement the Option A outer knot already uses (`Thunk ! {Div} T`); D1 moves it INSIDE the μ
so the self-reference carries it too.

### D2 — ρ is DECLARED, never inferred

Annotation grammar extends: `let rec f : Int -> Int ! {throws} = …` (absent `! {…}` ⟹ ρ = ∅,
today's behavior — fully backward compatible; every existing program elaborates identically).
The check is one monotone pass: elaborate the body under `f : recTy[ρ]`, require
`φ_body ⊆ ρ` (the #45 fold-payload arm with φ = ρ instead of ⊥). No fixpoint iteration, no
two-pass synthesis — the annotation is the fixpoint, supplied by the human/agent.

### D3 — inner self-calls type at ρ (Option A's under-approximation retires)

Under Option A the inner self-call was typed ⊥ (operationally harmless — Div has no runtime
semantics — but a lie for real effects). Under D1 the self-reference's type carries ρ, so
`($f) x` inside the body types at ρ like any other effectful call. The effective knot row
remains `ρ ∪ (structOK … ? ∅ : {divLabel})` — #47's certification stays orthogonal and keeps
firing (a structurally-terminating body with declared `{throws}` types as `{throws}`, not
`{throws, Div}`).

### D4 — what this does NOT decide (flagged for the ⊥-row⟹terminates work)

With rows on recursive types honest, the "⊥-row ⟹ terminates" soundness theorem becomes
STATEABLE (nothing pure-typed can recurse unboundedly except through the certified-total
fragment). This ADR makes the statement possible; proving it stays with the deferred
soundness work. Totality-refinement (structural recursion staying ⊥) is #47's lane, unchanged.

## Considered options

- **Declared row on the existing annotation (D2) — CHOSEN.** One-line explicit contract;
  single-pass check; rides the universal `! {…}` row syntax (zero new notation); backward
  compatible (no annotation = today's pure-rec). Cost: the programmer/agent writes the row —
  which the agent-first lens counts as a BENEFIT (the signature says what the function may do).
- **Fixpoint row inference — REJECTED.** Infer ρ by iterating body-synthesis to a fixed point
  (rows are finite ⟹ terminates). More machinery, and the contract becomes implicit: the row
  a caller sees depends on inference internals, and an effect added deep in a body silently
  widens every transitive signature. Violates config-explicit-at-boundaries and the lens.
  Note: NOT foreclosed — D2's `φ_body ⊆ ρ` premise is exactly the obligation inference would
  discharge, so inference can be ADDED later as sugar that computes the annotation.
- **Effect-polymorphic recursion (`ρ` a row VARIABLE in recTy) — REJECTED for v1.** Needs
  row-variable unification through μ-types — #56's full Rémy question. No v1 program requires
  a recursion whose row is polymorphic in its own definition; revisit with #56.
- **Keep rejection; η-expand through non-rec helpers — REJECTED.** The status quo workaround;
  fails the tokenizer dogfood (#50's motivating case) and buys nothing.

## Invariant compliance

- **#5 (five primitives)** / **#4 (calculated machine)**: untouched — elaborator-only; the
  kernel never sees the row (elaborate-to-mono, ADR-0075 precedent).
- **#2 (rows are sets)**: strengthened — one more place a row composes by the same join.
- **Stratification (ADR-0028)**: the Div seam stays type-visible and explicit; descent still
  marked, now with honest companion effects.

## Revisit if

- #56 lands subeffecting/Rémy → re-examine whether `φ_body ⊆ ρ` should become a coercion site
  and whether polymorphic recursion is then free.
- The ⊥-row⟹terminates proof needs a different row placement → this ADR's D1 is the frozen
  target; a placement change is a new ADR.
- Row-annotation ergonomics turn out noisy in practice (agents over-declaring `{Div}`
  everywhere) → consider the inference-as-sugar extension named in Considered options.

## Evidence

`Bang/Frontend/TypeCheck.lean:1698-1730` (Option A placement, `letRecRow`, `structOK`,
`.divMark` outer knot), `TypeCheck.lean:1012` (`.divMark` row insertion), #48 issue body (the
rejection repro + root cause), #46 closing comment (Option A scope + the named deferral of
full threading), #47 (`structOK` conservative-by-construction), ADR-0075 (elaborate-to-mono —
the pattern that keeps this kernel-free), ADR-0019/0020 (row placement canon).
