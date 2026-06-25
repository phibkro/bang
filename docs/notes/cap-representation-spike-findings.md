# Cap-representation feasibility spike — findings (→ ADR-0053 GO on absolute caps)

**VERDICT: GO on ABSOLUTE/LEVEL CAPS** (the 5→2). NO-GO on named handlers for v1.
Stay-seam-5 (ADR-0050) = the do-nothing baseline. Implemented: see ADR-0053; the 5→2
landed axiom-clean at `0435e88`, net **-112 LOC**.

This is the durable record of the spike that preceded the ADR-0053 implementation
(the brief: assess absolute-caps vs named-handlers vs stay-seam-5 to dissolve the
ADR-0050 shift wall). De-risk probes committed at `20fa7ab`:
`scratch/AbsoluteCapsProbe.lean` (shift dissolution) + `scratch/AbsoluteCapsStepProbe.lean`
(level↔index invariance against the real kernel).

---

## 0. The wall (ADR-0050, confirmed)

The 3 `crelK_fund` handler arms fail because `closeC_handle{Throws,State,Transaction}`
rewrite the body to close over `δ.map Val.shiftCap` (crossing the `handle` cap-binder
bumps ambient caps) while the IH delivers the unshifted `closeC δ M`. The bridge
(`EnvRelK_shiftCap`) reduces to a config-simulation `(handleF h :: K, shiftCap c) ≈ (K, c)`
that walls at the state/txn resume. Root cause: the **de-Bruijn cap SHIFT** (ADR-0046) —
a bang-specific artifact with no Biernacki proof to inherit (named handlers don't shift).

## 1. Absolute / level caps — GO (the 5→2)

**Dissolves the wall by construction (probe-proved).** Under absolute caps the `subst`
handle arm fills the body with the filler UNCHANGED (`abs_handle_no_shift`, by `rfl`), so
the config-sim becomes `(handleF h :: K, c) ≈ (K, c)` — `shiftCap = id`. The state/txn
resume case that killed routes A/B vanishes (stored caps are root-levels, obligation `s = s`).

**Level↔index dispatch invariance discharged sorry-free against the REAL kernel**
(`AbsoluteCapsStepProbe.lean`): `absSplit K lvl := staticSplit K (handlerCount K - 1 - lvl)`;
`absSplit_stable_under_top_push` / `migration_no_shift_needed` prove a root-level resolves to
the SAME handler across a top-`handleF` PUSH (migration) — the `+1` the de-Bruijn shift
threaded is absorbed by the conversion modulus (the two `+1`s cancel). `absSplit_decomp`
reuses the existing `staticSplit_decomp` verbatim.

**Cost measured near-zero where feared:**
- **CalcVM/Compile ignore the cap** (label-dispatched; `perform _ ℓ op v`) → ZERO blast
  radius there (refutes the brief's "CalcVM cascade" concern).
- STD block = **net DELETION + SIMPLIFY** (shift commutation theory + `HasVTy/HasCTy.shiftCap`
  deleted; 6 STD handle arms simplify to close like `letC`/`perform`). `shiftCap` was confined
  to 4 files (Operational/Metatheory/Compat/LR); Core/Syntax/Spec/EffectRow/CalcVM/Compile = 0.
- No 6th primitive; cap stays `Nat` (only its counting origin changes); set-rows untouched.

**Does NOT close `hcatch`/`:1801` alone** (the deferred 5→0) — those need the `CapResolves`
typing premise on `HasCTy.perform`, representation-independent; absolute caps make it
*tractable* (stable root level composes under migration). So absolute caps = the 5→2 win,
with 5→0 a separate increment.

## 2. Named handlers (ADR-0044) — NO-GO for v1

Dissolves the wall definitionally (names don't shift) AND closes **5→0 by construction**
(wrap-MISS + resume edge unrepresentable). BUT: a substrate change (Core `perform: Name→…` +
Syntax + fresh-name discipline); **VM re-derivation HIGH** (Bahr–Hutton re-runs a dispatch
arm — the opposite of absolute caps' ZERO); and a **possible 6th primitive** (ADR-0044's
Option B direct dispatch, library-encodability UNVERIFIED — a K-ADR-gated kernel-identity
change). Capability-as-value (Effekt) collapses into this. The principled **post-v1** direction.

## 3. Comparison (measured)

| axis | absolute caps | named handlers | stay seam-5 |
|---|---|---|---|
| dissolves wall by construction | YES (probe-proved) | YES | n/a |
| closes 3 arms (5→2) | YES | YES | NO |
| closes hcatch+:1801 (5→0) | NO (needs 1b premise, tractable) | YES | NO |
| CalcVM/Compile cost | **ZERO** (cap-agnostic) | HIGH (re-derive) | none |
| STD blast radius | net DELETION + simplify | substrate change | none |
| 6th-primitive risk | NO (5 primitives) | POSSIBLE | no |
| effort / risk | medium / low-med | high / high | none |
| v1-appropriate | **YES** | NO (post-v1) | yes (baseline) |

## 4. The one open obligation flagged INCONCLUSIVE — and its later resolution

The spike flagged the **level↔index dispatch theory's invariance under `Source.step`** as the
single un-build-grounded axis; it was then discharged sorry-free in `AbsoluteCapsStepProbe.lean`
(GO confirmed).

**BUT the implementation surfaced a DEEPER obligation the spike did not (the WC keystone) —**
recorded in ADR-0053 as the open 2c unit: `absResolvesKind`-WC is **NOT preserved under
handler-insertion-BELOW-use-site**. Inserting `handleF h` below an existing `handleF h₀` shifts
h₀'s absolute root-level, so a `perform` targeting h₀ (inside a thunk's own `handle h₀ …`)
mis-resolves (build-traced counterexample). The de-Bruijn `shiftCap` compensated exactly this.
The FILLER case (substFrom, caps target Sg, BELOW the insert) is the SAFE case and is discharged;
the keystone's recursion into thunk-internal handles is the unsafe case. Needs a different WC
formulation, NOT a mechanical re-proof — the deferred kernel-engineer/proof-engineer-paired unit.

## 5. Recommendation (adopted)

**GO on absolute caps for the 5→2** — smallest, lowest-risk change that dissolves the wall by
construction; costs measured near-zero (VM untouched) or net-negative (STD shrinks); keeps the
5 primitives. Named handlers stay the recorded **post-v1** direction (the structural 5→0 when
worth a substrate change). Implemented in ADR-0053.
