# 0060 — Cap-non-escape soundness via grade-driven liveness; commit the grade rig to NoZeroDivisors + ZeroSumFree + Nontrivial

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The diagonal's last obligation `wsCfg_step` (the `WScfg` preservation that closes
  `type_safety`) was UNPROVABLE as shaped — the POP arm's "deep B-occ lever" (a performable cap at a
  thunk-row position in `v:A` ⟹ `LabelOccurs ℓ A`) is **machine-checked FALSE** (`escapeB_app`: an
  arrow-guarded cap survives `app`-elimination into a `¬LabelOccurs` answer type; the language stays
  SOUND — the cap is operationally dead — so it is *invariant-too-strong*, not a soundness bug, not a
  `Spec.lean` change). A three-way build-checked survey refuted every **first-order** fix: (opt-1) a
  `▷`/later modality cannot intercept the thunk-reset leaf gate (`deep_cap_gate_fires`); (opt-2) a
  reachability flag closes POP but its force/β `dormant→live` promotion is false without `▷`
  (`promotion_is_false`); (opt-3 naive) a single-position `q≠0` gate is unsound — `q=0 ⇏ dead`
  (`q_zero_does_not_imply_dead`: budget-0 `ret (vvar 0)` uses a 0-graded var). **DECISION: grade-driven
  liveness** — a `Bool`-indexed `GRWSV/GRWSC` invariant whose gate is `b ∧ decide(q ≠ 0)` read
  *type-level* off the local `arr q A B` / `F q A` (NO grade-vector index ⇒ dodges the
  `[]=(q•γv)+γc` dependent-elim wall), threading liveness through every storage position. It dissolves
  all three walls (a forcing lam binds `q=1≠0`⇒live⇒no promotion; the budget-0 carry lands in a dormant
  slot; the deadness propagates coherently) and the subst bridge is **build-confirmed viable, not a
  wall**. The close **requires committing the grade rig `Mult` to three properties beyond
  `[CommSemiring][DecidableEq]`: NoZeroDivisors, ZeroSumFree (`a+b=0→a=0∧b=0`; RINGS fail), Nontrivial
  (`1≠0`)** — satisfied by the canonical `QTT={0,1,ω}` and `ℕ` (decide-confirmed). ADR-0057 B-occ is
  NOT replaced — it stays load-bearing for the *live*-cap-across-POP case; the liveness flag splits
  dormant (handled structurally) from live (B-occ-excluded). The full close (de-Bruijn joint bridge +
  live-cap-across-POP + the Model.lean port) is OPEN, tracked by task #41; DISPATCH resumption liveness
  ties task #35.
- **Refines**: 0057, 0056
- **Depends-on**: 0054, 0055, 0001, 0016
- **See-also**: 0025, 0030, 0058, 0059

## Status

Accepted (2026-06-26). Operator-ratified during the soundness-endgame session, on the strength of a
build-checked three-way survey + a build-confirmed (axiom-clean) viability spike for the chosen shape.
The grade-rig commitment is the operator's explicit ratification; the full proof close is scheduled
(task #41), build-gated, and does not change this decision.

## Context

### The wall (`wsCfg_step` POP arm)

The `Model` module (the soundness diagonal, on the inc-5 proof branch) proves `NonEscape (0,[],c)` for well-typed `VcapFree c` —
via a step-preserved unary invariant `WScfg` (`HasCTy ∧ HasStack ∧ WSC ∧ WSK`) with `WScfg ⇒
FocusResolves`. Its last `sorry` is `wsCfg_step` (the `WScfg` preservation). The POP arm
(`handleF g::K, ret v ↦ K, ret v`) needed: a value `v : A` returned past a popped handler at `⊥`
cannot expose a performable cap for the popped label. The sketched closure — "`¬LabelOccurs ℓ A` ⟹
every `ℓ`-cap in `v` is non-performable" — is **machine-checked FALSE**.

`escapeB_app` (committed, `inc5-lr-reindex`, axiom-clean) is the witness:

```
v := vthunk( app (lam (ret vunit)) (vthunk (perform (vcap g_h) "get" vunit)) )
```

`app` (Syntax.lean:168) *eliminates* the arrow, consuming the argument type `U (labelEff 1)(F q unit)`
that carries the cap; the result type is `A = U ⊥ (F 1 unit)` with `¬LabelOccurs 1 A` (a budget-0
return; `LabelOccurs` cannot see a label inside an eliminated arrow's domain). So a *performable*
`1`-cap sits inside `v` while `¬LabelOccurs 1 A` holds. The cap is operationally **dead** (the `lam`
discards its argument) ⇒ the **language is SOUND**; the chosen invariant is merely too strong. The
deadness is a TERM-level liveness fact, type-blind.

### The survey: three first-order fixes, all build-refuted

A parallel three-worktree survey (isolated branches, each a build-checked spike) eliminated every
first-order shape and, in doing so, triangulated the answer:

| option | shape | verdict (committed witness) |
|---|---|---|
| opt-1 | `▷`/later-LR on thunk/gate | the thunk-ambient-reset re-exposes the cap at its performable row; the leaf gate fires present-tense at every index ⇒ `▷` cannot intercept (`deep_cap_gate_fires`, `later_on_thunk_still_forces`). |
| opt-2 | reachability flag at storage positions | closes POP (`grwsv_dormant_deadcap`) but force/β needs a `dormant→live` promotion that is FALSE without `▷` (`promotion_is_false`). |
| opt-3 (naive) | single-position `q≠0` gate | UNSOUND: `q=0 ⇏ dead` — `lam (ret (vvar 0)) : arr 0 A (F 0 A)` types at `q=0` *using* var 0 (budget-0 return zeroes a used grade); `q_zero_does_not_imply_dead`. |

The structural convergence: the closing property is **liveness / non-occurrence** (opt-2), grade alone
does not witness it pointwise (opt-3 killer), and the storage commitment at an `appF` push precedes
the β-liveness — which *looked* like it forced step-indexing (opt-1). The escape was that **opt-2's
refutation mis-stored a `q≥1` (live) arg as dormant**; driving the liveness flag *by the grade* fixes
the storage rule and supplies the witness without a `▷`.

## Decision

**Grade-driven liveness.** Replace the performability gate (`labelEff ℓ ≤ ρ`) with a `Bool` liveness
index threaded through `GRWSV/GRWSC`, gated at each storage position by the **conjunction**
`b ∧ decide(q ≠ 0)`, where `q` is read TYPE-LEVEL off the local node:

- `app`-arg liveness ← the arrow multiplicity `q` in `arr q A B`;
- `ret`-value liveness ← the F-budget `q` in `F q A`;
- `letC`-bound liveness ← `q1` (since `q_or_1 q2 ≠ 0` always).

Because `q` lives in the *type index* (not the inert cap value, not a re-derived `HasVTy`), the gate is
a scalar `decide` with **no grade-vector index** — the `[]=(q•γv)+γc` dependent-elim wall that forced
the term+type indexing is **dodged**. The invariant stays `(K, Bool, term, type)`-indexed and inverts
cleanly.

This dissolves all three walls (build-confirmed, axiom-clean, `inc5-opt3-gradegate`):

- **opt-2's promotion** — `forcing_lam_binds_live`: a forcing lam binds `q = 1 ≠ 0`, so its arg is
  stored LIVE and the reduct consumes it at the same flag — the `dormant→live` promotion is never
  invoked (`reduce_forcing`).
- **opt-3's own killer** — `bridge_budget_zero_ret`: the budget-0 `ret (vvar 0)` stores its value at
  `b ∧ decide(0≠0) = false` (dormant), so the carried cap lands in a dormant slot with no obligation.
- **POP for the dead cap** — `grwsv_dormant_deadcap`: a `q=0` arg is dormant over *any* stack,
  including the popped one.

**The grade-rig commitment (ratified).** The grade↔flag bridge splits the typing grade through `•`
(scale) and `+` (add) nodes, concluding a factor is `0` from a product/sum being `0`. This requires
`Mult` to satisfy, **beyond `[CommSemiring][DecidableEq]`**:

1. **NoZeroDivisors** — `a * b = 0 → a = 0 ∨ b = 0` (the `•` / `ret` / `app`-scale nodes);
2. **ZeroSumFree** — `a + b = 0 → a = 0 ∧ b = 0` (the `+` / `letC` / `app` / `case` / `split` nodes);
3. **Nontrivial** — `(1 : Mult) ≠ 0` (the `letC` floor `q_or_1 q2 ≠ 0`).

The canonical `Bang.QTT = {0,1,ω}` and `ℕ` satisfy all three (`qtt_noZeroDivisors` / `qtt_zeroSumFree`
/ `qtt_nontrivial`, decide-closed). **Rings (e.g. ℤ) fail ZeroSumFree** — this is the property that
forbids the grade from being a ring. The commitment is judged *correct*, not merely acceptable: a QTT
grade is a resource count, and `ZeroSumFree` is exactly "resources cannot cancel / one cannot borrow
against a future use" — negative multiplicities are meaningless for QTT. It is a *generative*
constraint (it is what buys the bridge), in the spirit of invariant "constraints are generative."

**B-occ (ADR-0057) is refined, not replaced.** The liveness flag *splits* the POP obligation: a
DORMANT cap is stranded harmlessly (handled structurally by `decide(q≠0)`); a LIVE cap of the popped
label still forces `LabelOccurs ℓ A` and is excluded by the ADR-0057 B-occ premise. The two mechanisms
compose; the fix EXTENDS B-occ.

> **This decision's PROOF is OPEN — progress 2026-06-27, task #45 RESOLVED (`c63348b`) → `coh_step` →
> assembly; DISPATCH deferred (#35).** Build-confirmed axiom-clean ON `inc5-lr-reindex`
> (`c63348b`, `Bang.Model` green save the one `wsCfg_step` sorry): the full engine (live/dormant/mixed
> β subst bridge + POP wall + `⇒FocusResolves` + seed) PORTED to all 18 formers and the typeless
> `LWSV/LWSC/LWSK` invariant now carries `WScfg`; the typeless restack + MINT freshness; the rig bounds;
> the **`Coh` graded-mirror layer** (`LWSVg/LWSCg/LWSKg` + projection — the (A+) decision: the cap-bridge
> stays untouched, coherence is a SEPARATE layer, because (B-grade) would thread grade-arithmetic into
> the proven bridge and regress it — build-probed); and the discharge **rig + all non-`case`/`split`
> arms**. **Task #45 RESOLVED (`c63348b`, gate-verified):** the `case`/`split` scrutinee now gates at
> `b ∧ decide(q≠0)` — the consistent-gating fix (option 2: the SAME gate ret/app/appF already use; the
> scrutinee was the lone scaled position missing it), NOT the kernel `q≠0` restriction first weighed (that
> would make a SOUND `q=0` 'inspect-tag-discard-payload' program untypeable). Kernel byte-identical; the
> discharge `lwscg_to_lwsck` is WRITTEN + axiom-clean (⊆ {propext,Quot.sound}). STILL OPEN: (i) `coh_step`
> — the ~12-arm γ-preservation through `subst_value` (the multi-session crux). (ii) the `wsCfg_step`
> ASSEMBLY (pure wiring per opt-3's arm-map). **Do not cite `type_safety` as
> `sorryAx`-clean until `wsCfg_step` closes green** — it does NOT yet; the lone `Bang.Model` sorry is
> `wsCfg_step`. The decision is sound; the verification is the (now well-mapped) implementation.

## Consequences

- **Kernel constraint change.** `Mult`'s instance context gains `[NoZeroDivisors]` + a `ZeroSumFree`
  predicate + `Nontrivial` (`1≠0`). A grade semiring used to type bang must satisfy them; ℤ-style
  ring grades are excluded by construction. Added at the port (task #41), not retroactively.
- **`type_safety` mechanization route.** Soundness closes via the diagonal (route-β) with the
  grade-driven invariant — *first-order*, no step-indexed LR (the survey's negative result on opt-1
  is what makes the positive route worth the grind). Unaffected: the binary-LR / compiler-correctness
  path (ADR-0058) is independent.
- **Banked survivors carry over.** `escapeB_app` (the wall, build-pinned), `resolvesLabel_uncons`
  (POP mechanic), the three spikes' witnesses (`deep_cap_gate_fires`, `promotion_is_false`,
  `q_zero_does_not_imply_dead`) — all reusable; the spike branches are preserved as the evidence base.
- **Decided on build evidence, across three independent angles.** The survey refuted the alternatives
  by construction; the chosen shape is build-confirmed viable, not asserted.
- **Categorical reading (informative, not load-bearing).** A `cap ℓ` is a reference to an installed
  effect-algebra instance (the `handleF` frame); the QTT multiplicity bounds that reference's
  lifetime; a cap escapes its handler's extent only at grade 0, where "escape" is vacuous because the
  algebra is never dereferenced. Not formalized — the operational proof is canonical.

## Alternatives considered (rejected)

- **opt-1 — later/Kripke LR.** No `▷` placement closes POP without becoming the grade story; the
  thunk-reset leaf gate is present-tense at every index. Build-refuted (`deep_cap_gate_fires`).
- **opt-2 — reachability flag (ungraded).** Closes POP but its force/β promotion is false without
  `▷`. Build-refuted (`promotion_is_false`) — and its mis-stored-dormant `q≥1` arg is exactly what the
  grade-driven storage rule fixes.
- **opt-3 naive — single-position `q≠0` gate.** Unsound: `q=0 ⇏ dead`. Build-refuted
  (`q_zero_does_not_imply_dead`).
- **Keep `Mult` ring-compatible (no rig commitment).** Rejected: the bridge needs ZeroSumFree, which
  rings fail; and ring grades (negative resource counts) were never a sensible QTT model.
- **Defer to a step-indexed unary LR.** Was the recommended fallback *while* the survey read as
  "all first-order refuted"; superseded the moment the grade-driven candidate build-confirmed viable.
  Reconciling against the live tree (not the spike's interim message) is what caught it.
