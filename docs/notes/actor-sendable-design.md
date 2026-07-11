<!-- note-status: active -->
# Actor-send (`!`) sendable fragment — design (G7, POST-V1)

> Design-ahead. Feeds the concurrency-model ADR (NOT its own ADR). Grounds `wasm-concurrency-survey.md`
> §G7 resolution (i). Kernel witnesses: `Bang/Witness/SendableFragment.lean` (axiom-clean, in the gate).

## §1 · The problem (from the survey §G7 / §2a)

`!` (actor-send, ADR-0007) should have **one surface** with **two handler backends**: an in-process
scheduler `send` and a cross-component canonical-ABI call. But in-process naturally **SHARES** (one
GC-heap reference) while components **COPY** (lift/lower) — observably different the moment a
mutable-adjacent value crosses. Resolution (i): restrict `!` payloads to a **SENDABLE** fragment of
**deep-immutable** values, so copy ≡ share *observationally* and the two backends have one semantics.

## §2 · The fragment, precisely

`Sendable : Val → Prop` — first-order data closed over sendables:

```
Sendable vunit · Sendable (vint n)
Sendable (inl v) / (inr v) / (fold v)  ⇐ Sendable v
Sendable (pair a b)                    ⇐ Sendable a ∧ Sendable b
```

**Excluded** (the two heap-escapers of `memory-management-survey.md`):
- `vthunk M` — a **closure**: code + captured env. The canonical ABI has no way to lift a closure;
  sending one = sending code, which shared-nothing linking forbids.
- `vcap n ℓ` — a **handler identity**: meaningless across a component boundary, and *even in-process*
  a cap crossing actors is a cap **ESCAPING its handler's stack** (ADR-0063 `escapedCap`). Sendability
  excludes it → `!` over the fragment is escape-free by construction (`sendable_capsV_nil`).
- `vvar` — cannot occur in a *closed* value; excluding it makes `Sendable ⇒ Val.Closed` hold on the nose.

**Type-level mirror.** The sendable **surface types** are `unit`/`int` + `sum`/`prod`/`mu` over
sendables; **NOT** `U` (thunk), `arr`, or `cap`. It is a **plain predicate on `Ty`** — a value-shape
property — **not a row/grade citizen**. This follows the survey's G4 verdict (concurrency is
row-not-grade) *a fortiori*: sendability isn't even a row, it's a structural type predicate, the
same kind the CLI's `runYieldsInt` "closed term of ground type" convention already uses.

**Is Sendable = closed ground values? Nearly — it is the generalization.** `runYieldsInt` accepts a
*closed value of `int`*; Sendable is *closed value of `int`/`unit` + sums/products/μ over the same*.
So the fragment is the existing "closed ground value" notion **lifted from the base types to the
first-order ADT closure** — the repo already has the vocabulary; this names the ⊕/⊗/μ extension of it.
`Sendable ⊆ Val.Closed` is proven (`Sendable.closed`), tying it to the repo's `Val.Closed` (SSoT).

## §3 · THE THEOREM (copy ≡ share) — proven vs stated

Because a sendable value has **no `vthunk`** and **no `vcap`**, no `Source.step` arm can force code
or dispatch an effect *through it* (the only value-driven arms are `force (vthunk _)` and
`perform (vcap _ _) …`). So substituting a fresh **COPY** for a **SHARED** reference is invisible to
the machine. What is **PROVEN in Lean** (`Bang/Witness/SendableFragment.lean`, all axiom-clean):

| lemma | statement |
|---|---|
| closure + inversion | `Sendable` is a well-formed inductive over `inl/inr/pair/fold`; the excluded formers refute |
| `sendable_capsV_nil` | `Sendable v → capsV v = []` — no cap ⇒ **cannot escape** (ADR-0063 tie-in) |
| `sendable_shiftFrom_eq` | `Sendable v → Val.shiftFrom c v = v` (no free var to lift) |
| `Sendable.closed` | `Sendable v → Val.Closed v` (fixed by shift at every cutoff — the SSoT link) |
| `sendable_substFrom_eq` | **the fixed-point lemma**: `Sendable v → Val.substFrom k w v = v` — INERT under subst |
| `copy_eq_share_demo` | a sendable substituted-in (`unfold sVal`) vs bound-and-shared (`letC (ret sVal) …`) reach the **SAME** `Source.eval` outcome |

**Stated, riding the PARKED LR.** The **full contextual** form — *for all program contexts, copy and
share are observationally equivalent* — is contextual equivalence, which is **binary-LR territory**
(the LR is parked). This note **states** that theorem and proves its **syntactic backbone** (the six
lemmas above); the contextual closure is the LR's obligation, not a wall. Honest stratification: the
kernel-syntactic core is discharged now; the observational quotient waits on the parked LR. The
`sendable_substFrom_eq` fixed-point is *exactly* the substitution fact the contextual proof consumes.

## §4 · The escape story (the diagnostic)

**Today, if a non-sendable tried to cross `!`:** a **typing refusal at the `!` site** — the payload's
type must satisfy the `Ty`-level sendable predicate; a `U`/`arr`/`cap`-typed payload is rejected with
a B-code diagnostic (`error(bang.nonSendablePayload)`: "actor-send payload of type _ is not sendable;
it carries a thunk/handler that cannot cross an actor boundary"). This is a **static** refusal — the
fragment is a type predicate, checked where `!` elaborates, before any run.

**Future relaxations — named as out-of-scope DOORS, not designed here:**
1. **In-process thunk-send.** Two actors sharing a heap *could* send a `vthunk` as a **distinct,
   explicitly-marked** op (not `!`) — sharing a closure by reference is sound when there is no ABI copy.
   A separate future op with its own row label; not the unified `!`.
2. **Replicated mutable data.** `TVar`/CRDT sharing across actors is the **`distributed-story.md`** arc
   (CALM/`coord`, certified CRDTs). TVar-handles crossing actors is **explicitly OUT of scope** here —
   replicated data is CRDT territory, not the immutable-copy fragment.

## §5 · The performance corollary (the payoff — why (i) beats always-copy (iii))

Because of the theorem, the two backends may **use different strategies with identical semantics**:
the in-process backend **SHARES** (pass the GC-heap reference — zero copy) as a pure optimization,
while the component backend **COPIES** (canonical ABI lift/lower — forced by shared-nothing). Same
observable result, free efficiency. This is the whole reason resolution (i) beats always-copy (iii):
(iii) throws away in-process sharing to buy a uniformity the theorem already gives for free.

## §6 · Prior art (cited honestly)

| system | mechanism | relation to bang |
|---|---|---|
| **Erlang** | copy semantics over **immutable** terms; bignums/binaries share under-the-hood *because* immutable | THE precedent — "immutable ⇒ copy≡share" is our theorem, in production 30 years. bang's values are already immutable, so the fragment is the *first-order* slice of that. |
| **Rust `Send`** | a **trait** bound; `!Send` for `Rc`, raw pointers, etc. | the namesake. bang's version is *structural* (a value/type predicate), not a nominal trait — no coherence machinery, since immutability is already global. |
| **Swift `Sendable`** | marker protocol for concurrency-safe types | name collision, fine; same idea, protocol-shaped. |
| **Pony reference capabilities** (`iso`/`val`/`ref`/`box`/`tag`) | a **per-reference capability lattice** enforcing at-most-one-writer to make *mutable* data sendable | **evaluated and REJECTED as disproportionate.** Pony's ref-caps exist to send *mutable* state safely; bang's kernel values are **already deep-immutable**, so the entire ref-cap lattice buys nothing the `Sendable` predicate doesn't. Adopting it would add a heavyweight per-reference type system to solve a problem immutability already solves. The cheap structural predicate dominates. |

## §7 · ADR-input paragraph (for the concurrency-model ADR)

Adopt survey §G7 **resolution (i)**: `!` payloads are restricted to the **Sendable** fragment
(`Sendable : Val → Prop` / its `Ty` mirror — closed first-order data: `unit`/`int` + `sum`/`prod`/`mu`,
excluding `U`/`arr`/`cap`). This is *not* a new primitive, row, or grade — a **structural type
predicate** at the `!` site (invariant #2/#5 intact). It licenses **one surface `!` with two backends**
(in-process SHARE, component COPY) at *identical* semantics, justified by the kernel theorem
`copy ≡ share` (syntactic core proven axiom-clean in `Bang/Witness/SendableFragment.lean`; contextual
closure rides the parked binary LR). Reject Pony-style reference capabilities (disproportionate given
global immutability) and always-copy (iii) (discards free in-process sharing). Out-of-scope doors:
in-process thunk-send (a distinct marked op) and replicated-mutable-data (the CRDT/`coord` arc). This
paragraph is **input** to the concurrency-model ADR — it does not stand as its own ADR.

## Citations

`wasm-concurrency-survey.md` §G7/§2a/§3 (the two-backend problem; row-not-grade) · ADR-0007 (`!` =
actor-send) · ADR-0055/0063 (cap identity; `escapedCap` escape) · `memory-management-survey.md`
(closures = only heap escapers; the U grade) · `distributed-story.md` (CRDT/CALM arc — out of scope) ·
`os-inspiration-survey.md` (row-attenuation at the component `world` boundary) · Erlang (copy over
immutable terms) · Rust `Send` · Swift `Sendable` · Pony reference capabilities (rejected).
