# Plan 003: Thread the `effects` table through `runInferV` — close the fifth silently-missing-binder candidate

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git diff --stat f1cb2cf..HEAD -- Bang/Frontend/TypeCheck.lean`
> If the file changed since this plan was written, compare the "Current state"
> excerpts against the live code before proceeding; on a mismatch, treat it as
> a STOP condition.

## Status

- **Priority**: P2
- **Effort**: S
- **Risk**: LOW (default parameter keeps every existing call site behavior-identical)
- **Depends on**: none
- **Category**: bug (latent — possibly live; Step 1 decides which)
- **Planned at**: commit `f1cb2cf`, 2026-07-10

## Why this matters

This codebase has a documented bug family (four fixed members, issues #85/#86 among them): an inner elaboration/inference run is seeded with an **empty state** — missing the `effects` table or binder context — and fails *silently* whenever a user-defined-effect operation is reached through that path. The fix pattern is established: add an `effects` parameter with default `[]` and seed the inference state with it (see the fix and its rationale in the doc comment quoted below).

`runInferV` is the fifth function with the pre-fix shape: it runs `.run' {}` — a fresh, effects-less state. Its sibling `zonkInferC`, two definitions below, already received the fix. If any of `runInferV`'s call sites can reach a user-effect `.dotPerform` (note: *values include thunks, and thunk bodies are computations that may perform*), the bug is live today; if not, it is latent and will fire silently the first time one can. Either way the fix is the same 3-line change, and this plan also pins the answer with a probe.

## Current state

- `Bang/Frontend/TypeCheck.lean:884-889` — the pre-fix function (verbatim):

```lean
/-- Run an inference action from an empty state, zonk, and zonk-EXTRACT to a kernel `VTy` (the concrete
answer the elaborator's resolution sites + the boundary need). A residual value hole extracts to a
reserved-range `tvar`; a residual comp hole fails loud. -/
def runInferV (act : Infer IVTy) : Except String VT := do
  let iv ← (do zonkV bigFuel (← act)).run' {}
  extractV iv
```

- `Bang/Frontend/TypeCheck.lean:890-899` — the sibling that already has the fix, INCLUDING the doc comment explaining the bug class (verbatim; your new doc comment should reference this one rather than duplicate it):

```lean
/-- As `runInferC`, but keep the ZONKED `ICTy` (no extraction) — for the elaborator's chole-tolerant
returner probes (`anfSplit`, `let`-RHS), which must inspect a higher-order result WITHOUT failing on a
still-open computation hole. `effects` (ADR-0092 D2, #21 s7probe WALL-3-class fix, default `[]`):
`.run' {}` seeded a FRESH, effects-less `USt` here too (the SAME class of bug `elabBind` had —
`anfSplit`'s `synthSC Γ e'` throwaway run hits `.dotPerform`'s D2 arm on ANY A-normalized user-effect
perform, e.g. `net.fetch(1) + 1`, which needs `handleCustomS`'s A-normalization to see `net`'s
resolved label). Every PRE-existing call site is decl-free or doesn't need `.dotPerform` against a
user effect, so the default keeps them behaviour-identical. -/
def zonkInferC (act : Infer (ICTy × Row)) (effects : List (String × EffectInfo) := []) : Except String (ICTy × EffRow) :=
  (do let (B, φ) ← act; return (← zonkC bigFuel B, (← resolveRow bigFuel φ).labels)).run' { effects := effects }
```

- `runInferV` call sites (all in the same file, all pass `synthSV Γ… <value>`): lines **2650, 2661, 2696, 2717, 2745**. At each site, an `effects`/`env.effects` value may or may not be in scope — Step 3 investigates before threading.

## Commands you will need

| Purpose | Command | Expected on success |
|---|---|---|
| Enter dev shell | `nix develop` | banner |
| Fast single-file check | `nix develop --command just check Bang/Frontend/TypeCheck.lean` | `✓ no errors or warnings` |
| Compiled guard gate | `nix develop --command lake build` | exit 0 |
| Run a probe program | `nix develop --command bash -c 'lake build bang >&2 && echo "<prog>" > /tmp/probe.bang && .lake/build/bin/bang check /tmp/probe.bang'` | typing verdict on stdout |
| Full gate | `nix develop --command just verify` | exit 0 |

## Scope

**In scope**:
- `Bang/Frontend/TypeCheck.lean` — the `runInferV` definition, its doc comment, its call sites (only if Step 3 finds a live path), and one or two new `#guard`s in the guard region at the bottom of the file.
- `plans/README.md` (status row)

**Out of scope** (do NOT touch):
- `zonkInferC`, `runInferC`, `synthSV`, `synthSC` — the fix is at `runInferV`'s state-seeding only.
- Any file under `Bang/Core/`, `Bang/Spec.lean`, `Bang/Meta/`, `Bang/Backend/`.
- Any `theorem` (the pre-commit statement-change detector fires on `theorem` line changes; this plan should produce none).

## Steps

### Step 1: Probe — is the bug live?

Write this program to `/tmp/probe.bang` (a user-effect perform inside a THUNK bound by `let`, inside a handle — the shape that reaches value-inference on a computation-carrying value):

```
effect Net { fetch : Int -> Int }
handle
  (let t = {net.fetch(1)} in $t) + 0
with Net as net {
  fetch(n) => n * 10
}
```

Run `bang check /tmp/probe.bang` (command table above). Record the outcome:
- **Types cleanly** → the bug is latent (thunk-typed values at those call sites don't descend into performs, or the sites never see this shape). Proceed with the defensive fix.
- **Fails with an effect-resolution error** mentioning `net`/`fetch`/unknown effect while the same program WITHOUT the `let t = {…}` wrapper (i.e. `net.fetch(1) + 0`) types cleanly → **the bug is live**; this plan fixes it, and the probe becomes the regression guard in Step 4.
- Fails with a *parse* error → the probe shape isn't v1-expressible; try the variant `(let t = {net.fetch(1)} in $t)` without the `+ 0`. If still unparseable, proceed as "latent" and note it.

**Verify**: you have a recorded verdict (live / latent) with the exact diagnostic text.

### Step 2: Apply the fix

Change `runInferV` to (matching `zonkInferC`'s pattern exactly):

```lean
def runInferV (act : Infer IVTy) (effects : List (String × EffectInfo) := []) : Except String VT := do
  let iv ← (do zonkV bigFuel (← act)).run' { effects := effects }
  extractV iv
```

Extend the doc comment with one sentence, e.g.: `` `effects` (default `[]`): same WALL-3-class seeding fix as `zonkInferC` below — a fresh `USt` here dropped the effects table for any value inference that descends into a user-effect perform. ``

**Verify**: `nix develop --command just check Bang/Frontend/TypeCheck.lean` → `✓ no errors or warnings` (all call sites still compile via the default).

### Step 3: Thread call sites (only if Step 1 said LIVE)

If the probe failed in Step 1: at each of the five call sites (lines ~2650, 2661, 2696, 2717, 2745 pre-drift), determine whether an effects table (`env.effects` or a local `effects`) is in scope, and pass it: `runInferV (synthSV Γ1 sv) env.effects`. Model on how `zonkInferC`'s callers pass theirs (search `zonkInferC (` for exemplars). If no effects value is in scope at a site, trace one parameter level up — the callers of that function will have it; extend at most ONE level, otherwise STOP (see below).

If Step 1 said LATENT: skip this step — the default `[]` keeps sites behavior-identical, and the parameter exists for the future path.

**Verify**: `nix develop --command just check Bang/Frontend/TypeCheck.lean` → clean; if LIVE, re-run the Step-1 probe → now types cleanly.

### Step 4: Pin with a #guard

In the guard region at the bottom of the file (after line 5319's corpus; follow plan 002's section if it landed), add:

- If LIVE: a `#guard` asserting the Step-1 probe program now TYPES (use the corpus's `checkProg`-style idiom — read neighboring guards for the exact helper), with a comment naming it the fifth family member's regression pin.
- If LATENT: a `#guard` asserting the probe program types (it already did — the pin prevents the future regression), commented as pinning the `runInferV` seeding contract.

**Verify**: `nix develop --command lake build` → exit 0.

### Step 5: Full gate + commit

Commit style: `fix(frontend): thread effects through runInferV — the fifth WALL-3-class seeding (plan 003)` (adjust `fix`→`refactor` if Step 1 said latent).

**Verify**: `nix develop --command just verify` → exit 0; `git status --porcelain` clean apart from in-scope files.

## Test plan

- The Step-1 probe program as a compiled `#guard` (regression pin), placed in the ADR-0095 corpus region.
- If LIVE: also add the probe as `examples/`-style coverage ONLY if an existing example directory naturally extends (optional; the guard is the required pin).
- Existing batteries (`just verify`) confirm no behavior change at the five call sites.

## Done criteria

- [ ] `runInferV` has the `effects` parameter seeding `.run' { effects := effects }`
- [ ] Doc comment updated referencing the `zonkInferC` precedent
- [ ] Step-1 verdict (live/latent) recorded in the commit message body
- [ ] ≥1 new `#guard` pinning the probe shape
- [ ] `nix develop --command just verify` exits 0
- [ ] No `theorem` lines changed (`git diff | grep -E '^[+-].*theorem'` → empty)
- [ ] `plans/README.md` status row updated

## STOP conditions

Stop and report back (do not improvise) if:

- Step 3 requires threading `effects` more than ONE parameter level up from a call site — the change is metastasizing beyond a seeding fix; report the call chain instead.
- The Step-1 probe fails with a diagnostic that does NOT implicate effect resolution (e.g. a kernel typing error about thunks/force) — that's a different finding; report it, apply only the defensive Step-2 change.
- Any existing battery or `#guard` breaks after Step 2 — the default-parameter assumption is wrong somewhere; report which gate.

## Maintenance notes

- This closes the KNOWN five-member seeding family (`elabBind`, `anfSplit`/`zonkInferC`, `elabHClauses`, `curryBind`, `runInferV`). The structural end-state (suggested by the engineer who fixed #85/#86): a lint or review rule that any `.run' {…}` seeding an inference state must either thread `effects` or carry a comment justifying the empty table. Consider filing that as an issue when this lands.
- Reviewer should scrutinize: that call sites were only threaded if the probe proved a live path (avoid speculative plumbing), and that the doc comment says WHY the parameter exists.
