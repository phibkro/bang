# Core implementation — architectural overview

> The map of *what we've built and how the pieces couple* — so we can reason about which decisions
> reinforce each other and which work against each other. Code is the source of truth; this is the
> approximation that makes the coupling **visible** (the thing whose absence let ADR-0053's cap bug hide).
> Generated-where-possible, hand-written for the interaction judgement. Links to ADRs/refs, never restates them.

## 1. The pipeline (ADR-0016, architecture in force)

```
  source  ──►  graded-CBPV semantics  ──►  CalcVM (Bahr–Hutton)  ──►  WasmFX (Benton–Hur LR)
              the executable spec          calculated machine        verified compiler output
```

Two verification spines ride this: the **calculated VM** (`compile, Code, exec` derived from `eval`) and
the **step-indexed logical relation** (`lr_sound`/`lr_fundamental`, the Compat layer) that backs
`compile_forward_sim`. Both are checked against `exec` (invariant #1: proof rides the reference).

## 2. The module graph — the "V" (enforced by `tools/arch-check.sh`)

```
            EffectRow (194)                    fan-in = # modules importing it · (LOC)
                │
              Core (320) ◄──────────── 7        ★ shared apex of the V
            ┌───┴───────────────┐
       Frontend edge        Backend edge        Frontend and Backend meet ONLY at Core
       Syntax (333) ◄─ 6     Operational (949) ◄─ 9   ★ THE HUB
       Surface (759)         ├ Metatheory (3501)
       Surface.Trait (411)   ├ LR (1134)
       Frontend.NamedCore    ├ CalcVM (4320)   ─┐ deferred RED (route-B, ADR-0052)
                             ├ Compile (3310)  ─┤
                             ├ Compat (2280)    │ green subset = Core·Syntax·Operational·
                             └ Surface          ┘ Metatheory·LR·Compat (lake build Bang.Compat)
                │
              Spec (282) ◄──── fan-out 7         ★ THE APEX — frozen theorems tie everything

  side cluster (paused, ADR-0015):  Mult · CalcReify · CalcReifyRef · CalcReifySim(1433)
```

**What the shape reveals** (from `import` DAG + per-symbol reference counts):

- **`Operational` is the single load-bearing hub** (fan-in 9). Healthy otherwise: complexity lives in the
  big *leaves* (CalcVM/Metatheory/Compile/Compat, fan-in 1–2 — write-once proof bodies), coupling lives in
  the *small* core (Core/Syntax/Operational). The hub is the exception: small-ish, but high fan-in **and**
  high internal density.
- **The "V" is real and enforced**: Frontend (Surface/Syntax/NamedCore) and Backend (CalcVM/Compile) cannot
  reach into each other; they meet only at Core.

## 3. The coupling map — cross-cutting representations (the part that bites)

A concern's *blast radius* is how many modules reference it, independent of the import graph:

| concern | # modules | reads as… |
|---|---|---|
| effect rows (`Eff`/`labelEff`) | 14 | total pervasion — the type-level spine (by design, ADR-0001/0018) |
| `handlesOp` (dispatch) | 9 | effect dispatch is everywhere → the ADR-0054 blast radius |
| `substFrom`/`shiftFrom` | 7 | substitution pervasive |
| `splitAt` (LEGACY dynamic dispatch) | 6 | still smeared despite ADR-0045 static dispatch → **debt** |
| caps (`CapResolves`/`staticSplit`/`shiftCap`) | 4–5 | the cap representation — **kernel-confined, NOT in CalcVM/Compile** |
| `closeC` | 4 | `closeC ≡ Comp.subst`, in LR/Compat/Metatheory — **the bug's fingerprint** |

### The missing seam (architectural root of the ADR-0053 mistake)

The cap representation lives in `Operational` (the hub) **and** is mirrored by `closeC ≡ subst` in the LR.
There is **no boundary isolating "how dispatch resolves a handler" from "how subst/closeC closes an
environment"** — so any cap change must stay consistent across the kernel↔LR seam *simultaneously*.

```
  cap representation is load-bearing in FOUR places at once:
     kernel dispatch (absSplit) · Comp.subst · LR closeC(≡subst) · CalcVM evalD
                                       └──────── the SAME function ────────┘
```

That absent seam is why absolute caps *looked* safe in isolation: nothing showed that a substitution-time
shift (migration soundness) and an unshifted `closeC` (the LR 5→2 win) are the **same knob in opposite
positions**. ADR-0054's generative-identity representation **decouples** them (a stable identity → `subst`
doesn't shift → `closeC` mirrors no shift → the kernel↔LR cap-consistency obligation disappears).

## 4. Symbol coupling — file boundaries vs logical units

Move-analysis (symbol defined in A, used predominantly in B) shows three places where **file boundaries do
not match logical units**:

```
1. LR defines, Compat uses — nearly ONE unit split across two files
     closeC 86/90 · closeV 72/72 · VrelK 71/71 · CrelK 63/68 · KrelS 87/89 · EnvRelK 37/38  → in Compat
   LR.lean = "the relation DEFINITIONS", Compat.lean = "the fundamental-theorem PROOFS over them".

2. MISLOCATED: Stack.plug / Cxt.plug — defined in LR, used 80/89× in COMPILE
   machine/continuation ops living in the relation file, serving the backend → wrong layer.

3. The HUB is overloaded: Operational = kernel-reduction + cap-dispatch + LWT-invariants + substitution
   (FOUR concerns, fan-in 9). The reason the cap concern smeared and the seam above is missing.
```

## 5. Decision interaction — what reinforces vs what fights

```
  REINFORCING                                         IN TENSION
  ─────────────────────────────────────────────────────────────────────────────────────────
  effect rows = sets (0001/0018)                      LR-simplicity  ⟂  migration-soundness
    → lacks-discipline → no_accidental_handling          single-int cap: absolute(0053, unsound)
    → drops Biernacki ρ-maps (0024)                       vs relative+shift(0046, LR wall)
  STM-as-handler (0030) → 5 primitives hold              → resolved by identity caps (0054)
  calculated VM (0016) — machine is an OUTPUT          dynamic dispatch(0023/0024) vs static(0045)
  stratification: verified core + tested superset        → kernel vs evalD DISAGREE (0052, lexical)
    at a typed seam (0026/0028)                        the dispatch⟂subst HUB coupling (this doc §3)
```

The single most useful entry: **`LR-simplicity ⟂ migration-soundness`** — the axis ADR-0053 (unsound) and
ADR-0054 (the fix) live on, and the reason a representation change is forced rather than a patch (the shared
`subst`/`closeC` knob, §3).

## 6. Cleanup + restructuring (status + target)

### Done
- **−316 LOC**: the dead `WellCapped`/`WCComp` island removed from the hub (superseded by `LWConfig`,
  ADR-0045). `Operational` 1265 → 949. Verified `lake build Bang.Compat` = 711 jobs green. (`d1f0916`)

### NOT dead (corrected)
- **CalcReify\*** (~1850 LOC) is the ADR-0015 *paused reification frontier* (multi-shot/non-tail handler
  representation), deliberately in the build so its #guards gate — **not** the ADR-0051 rejected recast.

### Target restructuring (gated on the tree being green — see below)
```
  split Operational along its 4 concerns:
     Bang.Kernel       (reduction · Source.step · eval)
     Bang.Dispatch     (staticSplit/absSplit · handlesOp · the cap-resolution surface)
     Bang.Invariants   (LWT · LWConfig · HasConfig)
     Bang.Subst        (shiftFrom · substFrom · the closeC-mirrored substitution theory)
  relocate Stack.plug / Cxt.plug  LR → the machine layer (Operational/Kernel), where Compile uses them
  reorganise LR/Compat around logical units (value-rel · stack-rel · compat-lemmas), not def-vs-proof
  prune: legacy splitAt (6 modules) once dispatch settles; the orphaned WC helpers (CtxKindEq, hframes…)
```

**Timing.** The restructuring is entangled with the **red-by-design** build (deferred CalcVM route-B,
ADR-0052): `plug` is used by Compile (red), and splitting `Operational` rewrites imports in all 9
dependents including red CalcVM/Compile/Surface — module-boundary moves there cannot be *verified* until the
tree gates green. So execute the code-moves **after** the CalcVM route-B lands (or as tightly-scoped moves
contained within the green subset). Doing them now would add unverifiable changes to red modules — the exact
way a hidden break hides.

### Module system + deep-module target (verified v4.30, 2026-06-26 spike)

The toolchain (Lean v4.30) ships the **module system**, and a spike empirically gated what it buys us.
This **revises the "many public peers" target above** — the real target is deep modules
(directories with hidden internals), not a flat split.

**What the spike verified (empirically gated, not from docs):**
- The module system IS available and **HEADER-DRIVEN** — a `module` line at the top of a file; **no
  lakefile change**. `module` / `public` / `public import` all parse.
- A non-`public` def is **HIDDEN from importers** (cross-file encapsulation) — and even **CLASSIC
  (non-module) importers respect it**. The boundary holds regardless of whether the importer opted in.
- Module mode is **PRIVATE-BY-DEFAULT**: a plain `def` is module-local; `public` opts into the
  interface. **Mathlib-interop works** — module files import and use Mathlib normally.

**→ Incremental BOTTOM-UP migration is viable.** Module-ify a leaf, mark its internals non-`public`,
and its (still-classic) importers automatically see only the public interface AND still compile.
**No big-bang.** The v4.30 module system **dissolves the encapsulation-vs-incrementality tradeoff**
that forced the earlier flat-peer target.

**DEEP-MODULE TARGET (revised).** Not single large files, not many flat peers, but
**DIRECTORIES-WITH-HIDDEN-INTERNALS** — ~12 public modules:

```
  Algebra · Syntax · Typing · Semantics · Safety · Model(=LR+Compat)
  · CalcVM · Compile · Surface · Spec · Audit · Witness
```

Each module = a `module` **barrel** re-exporting only its `public` interface; the internals are plain
files (non-`public`), hidden behind it.

**SEQUENCING.** The restructure **TRAILS GREEN, module-by-module** — each module is restructured +
module-ified **the moment inc-5/inc-6 greens it** (boundary moves in still-red modules stay
unverifiable until then, per §6 "Timing" above). Module-ify **bottom-up** (leaves first).

## See also
- ADR-0016 (architecture in force) · ADR-0054 (the cap representation) · ADR-0052 (CalcVM route-B, the red)
- `CLAUDE.md` (the stratification principle, the invariants) · `tools/arch-check.sh` (the V fitness function)
