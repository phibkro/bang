# PATH — ◊5 Piece B: the dispatch transfer lemma (the last GAP-2 obligation)

**Status:** the ONLY remaining sorry on the ◊5 handler path. Everything else is proven +
committed on `cap5-compiler @ ef76e71` (model fix, Piece A handler-complete exec→wexec, the
Piece-B spine + the reverse bridge TOTAL except this one arm). When this lands,
`compile_forward_sim` (ungated, all handlers) → trusted-three = **◊5 GAP-2 CLOSED**.

> Effort, not uncertainty: this is the REVERSE of `run_evalD`'s raise-part — the machinery is
> proven and the forward correspondence is established. Multi-session (same weight as run_evalD's
> raise+term parts), cleanly isolated. Designed by the discovery IC (d5fix) before stand-down.

## Base
`cap5-compiler @ ef76e71` (worktree `../lang-bang-d5`). Gate: `nix develop --command lake build`
+ `lake env lean Bang/Audit.lean`. `compile_forward_sim_pure` is trusted-three (keep it —
a regression here is the known hazard; see DISCIPLINE). `just verify` is wedged on the loogle
re-clone — gate via `lake build Bang` + audit directly, documented.

## The obligation (the sorry at `evalD_complete_gen`'s `up` arm)

```
(K, up ℓ op v) ──Source.step──▸ dispatch K ℓ op v = some (K', focus)
given   Config.run F' (K', focus) = done w'     [IH: evalD of (K', focus)]
prove   ∃ m, evalD m [] [] (plug K (up ℓ op v)) = some (.term (.ret w'), [], [])
```

Lemma to prove — `evalD_plug_dispatch`:
```
theorem evalD_plug_dispatch (K) (ℓ op v) {K' focus}
  (hd : dispatch K ℓ op v = some (K', focus))
  (hn : evalD n [] [] (plug K' focus) = some (.term (.ret w'), [], [])) :
  ∃ m, evalD m [] [] (plug K (up ℓ op v)) = some (.term (.ret w'), [], [])
```

## The crux — the ONE genuinely new lemma: `evalD_plug_descend`

Evaluating `plug K c` at `[] []` EQUALS evaluating `c` at the accumulated stores
`(ctxStates K, ctxTxns K)`, modulo the handle pop/forward post-processing per K's handleF frames:
```
evalD n [] [] (plug K c)  ≈  (evalD n' (ctxStates K) (ctxTxns K) c) >>= (pop/forward per K's handleF)
```
This is the REVERSE-direction analog of how `run_evalD` threads σ/τ FORWARD. The forward
correspondences are already defined: `CtxCorr σ K = (σ = ctxStates K)` (CalcVM:2546), `CtxTxnCorr
τ K = (τ = ctxTxns K)` (CalcVM:2570). **`evalD_plug_descend` is the only piece not yet in the
repo; everything else reuses.** Plus the `splitAt`-decomposition of `plug K` at the evalD level
(the `Kᵢ/handle/Kₒ` split).

**v2 implementation detail (the design IC source-checked these — start here):**
- Exact statement: `evalD n [] [] (plug K c) = (evalD n c (ctxStates K) (ctxTxns K)) >>= postK`,
  where `postK` applies K's handleF pop/forward chain to the body outcome (the SAME pop/forward
  `evalD`'s handle arm does, lifted over the K-prefix). **Prove by induction on K** (the handleF
  case pushes one store + composes one pop into `postK`; letF/appF wrap the focus, no store change).
- **THE TRAP — store accumulation ORDER.** `ctxStates` collects state-frame values
  INNERMOST-FIRST: `handleF (state ℓ s) :: K => (ℓ,s) :: ctxStates K`. This matches `evalD`'s push
  order (`plug` wraps outermost-first; `evalD` pushes as it descends ⇒ the innermost handle's store
  is deepest = LAST pushed = HEAD of σ). Get the store order right or the descend won't typecheck —
  this is the MEDIUM-risk bookkeeping.
- **No shortcut via the forward bridge:** `dispatchRun n K ℓ op v = Config.run (n+1) (K, up ℓ op v)`
  (CalcVM:2528) is SOURCE-side (`Config.run`), NOT `evalD`. So the forward lemmas are reused as
  FACTS, not inverted wholesale; the dispatch arm genuinely needs the reverse argument.
- `splitAt↔plug` decomposition: `plug K = plug Kₒ ∘ handle h ∘ plug Kᵢ` at the catching frame —
  aligns the descend with `dispatchOn`'s `Kᵢ/h/Kₒ` split. `evalD` up-arm forks at CalcVM:213-229
  exactly as `dispatchOn` (Operational:277).

## The 3 sub-cases (case on `splitAt K ℓ op = some (Kᵢ, h, Kₒ)`; mirror `dispatchOn`, Operational:277)

1. **throws ℓ' → ABORT.** `K'=Kₒ`, `focus=ret v`. The up-arm RAISES (no σ/τ service for a throws
   label); the raise propagates up through `Kᵢ`'s handles (each forwards via the tail — evalD
   handle arm's `.raised` branch pops + forwards) to the throws handle, whose throws-arm CATCHES
   (`ℓ'=ℓ ∧ op=raise`) → yields `ret v` over `Kₒ`. REUSE: `dispatchRun_handleF_skip` / the
   `run_evalD` RAISED-part forwarding (CalcVM:3549, 3969+). ▷-free.
2. **state ℓ' s → RESUME.** `K'=Kᵢ++handleF(state ℓ' s')::Kₒ`, `focus=ret s` (get) / `ret unit`
   (put). The up-arm SERVICES get/put against `σ=ctxStates K` (the matching state frame), threads
   `σ'`, returns `ret s/unit` — matching the resumed config. REUSE: `dispatch_state_get`/`_put`
   (CalcVM:3096/3178) — the EXACT forward facts, applied in reverse.
3. **transaction ℓ' Θ → RESUME.** `K'=Kᵢ++handleF(transaction ℓ' Θ')::Kₒ`, `focus=ret r`. The
   up-arm services the txn op against `τ=ctxTxns K` via `txnService`, threads `τ'`. REUSE:
   `dispatch_txn_service` (CalcVM:3376).

## Reuse map (verbatim / adapt / new)

- **VERBATIM:** `CtxCorr`/`CtxTxnCorr`/`ctxStates`/`ctxTxns`/`ctxNetEffect` (defs),
  `dispatch_state_get`/`_put`, `dispatch_txn_service`, `dispatchRun_handleF_skip`, `ctxNetEffect_self`.
- **ADAPT (reverse direction):** `run_evalD`'s TERM-part up-arm (CalcVM:3688-3771, the
  get/put/txn service) → run BACKWARD; `run_evalD`'s RAISED-part forwarding (3969+) → the abort
  propagation.
- **NEW:** `evalD_plug_descend` (the `[] []`→`(ctxStates K, ctxTxns K)` bridge — the crux) +
  the `splitAt`-decomposition of `plug K` at the evalD level.

## Size / risk

Multi-session (same weight as `run_evalD`'s raise+term parts, which are large). **Feasibility
risk LOW** (machinery proven, forward correspondence established). **Bookkeeping risk MEDIUM** —
the reverse store-threading in `evalD_plug_descend` is the fiddly part (the kind that bit ◊4.5b's
scratch probes). NO conceptual unknown: the proven forward bridge, reversed.

## Plan

Start with the crux: **`evalD_plug_descend`** — source-check its exact statement against
`ctxStates`/`ctxTxns`/the handle pop-forward semantics FIRST (flag-before-build), then prove it.
Then `evalD_plug_dispatch` (the 3 sub-cases over the proven descend + the reused forward facts).
Commit FREQUENTLY (multi-session). Gate each chunk. Final: discharge the `up`-arm sorry →
`compile_forward_sim` (ungated) → trusted-three; keep `compile_forward_sim_pure` trusted-three
(the separate sorry-free `evalD_complete_gen_pure` already isolates it — do NOT re-route the pure
headline through the total bridge). Independent merge-gate by the orchestrator.

## Discipline

- Gate the AXIOM SET on committed content (#print axioms), not the green build — the pure headline
  silently regressed once (caught pre-commit); watch for it on every commit.
- flag-before-build on `evalD_plug_descend`'s statement; STOP+report a precise wall over grinding.
- Self-report saturation at a clean checkpoint → hand off via the committed branch.
