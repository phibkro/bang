# PATH — inc-6: CalcVM route-B (cap-keyed `evalD` re-derivation)

> In-flight work doc for **task #15**. Two halves: the **method grounding** (the
> Bahr–Hutton calculated-compiler literature, why route-B is a *re-calculation*) and
> the **build-arbitrated scoping map** (what's actually broken, the unit plan, the
> wall-risk). SoT for the CONTROL/dispatch calculation; ADR-0052 is the decision.

## 0. The one-sentence frame

**route-B = re-derive `evalD` as the big-step denotation of the *new* (identity-dispatch) kernel
`Source.step`, then re-calculate `compile`/`exec`/the bridge from it — a CALCULATION, not a patch.**
The stale CalcVM is the *old* (dynamic / nearest-label) calculation; its errors are that derivation
breaking under (i) the ADR-0054 identity AST and (ii) the dynamic→cap-keyed semantic switch.

## 1. Method grounding — the Bahr–Hutton stack (the literature is on our side)

bang already stands on two of the three layers; route-B adds the third.

| layer | paper (`references/papers/2-calcvm/`) | technique | bang status |
|---|---|---|---|
| **divergence** | monadic '22 (`monadic-compiler-calculation`) | partiality monad + **strong** bisimilarity (strong, not weak — it supports *equational* calculation; the calc inserts the right number of target steps to align) | **adopted** (`Comp` is partial; calc rides bisimilarity/fuel) |
| **effects** | garby '24 (`garby-haskell24-calculating-effectively`) | algebraic effects; effect **interpretation decoupled** from the calculation (so the calc is identical regardless of how state is realized) | **adopted** (`SStore`/`THeap` = the decoupled state interpretation) |
| **control** | **concurrency '23** (`bahr-hutton-icfp23-calculating-compilers-concurrency`) | **codensity monad over choice trees** + bisimilarity — the key ingredient for calculating *control* compilers (fork, channels) | **the new layer** — handler dispatch is control |

**The load-bearing inspiration:**
1. **Not inventing the method, applying it.** The discipline (specify `exec (compile M) s ≅ do v ← evalD M; exec c (v:s)` over the partiality monad + strong bisimilarity, induct, `Code`/`exec` *fall out* correct-by-construction) is monadic'22 + garby'24, which bang already uses.
2. **Control = continuation-capture; codensity makes it calculable.** concurrency'23's key move: control (fork — and by extension **handlers**) is a continuation-capture, and the **codensity** construction (`∀r. (a → CTree r) → CTree r`) makes that continuation-passing clean + monadic + calculable. For bang: a `perform` captures a continuation, the handler resumes it — that is the codensity `∀r`. The cap-keyed dispatch Code should *fall out* of `exec (compile (perform cap)) ≅ evalD (perform cap)`, the continuation being the codensity argument. **Use this as the conceptual frame for the dispatch derivation** even though our `evalD` is stateful-CK, not literally choice-tree-based.
3. **Open niche, confirmed from source.** garby §6 names first-class **handlers** as *unsolved*; concurrency'23 is the *nearest* (channels/fork, not handlers). **bang's calculated handler-dispatch compiler is genuinely novel** — the reason CalcVM exists (invariant #4). No template to copy; the *method* transfers, the dispatch Code is ours to derive.
4. **Defunctionalization alternative** (Ager '03, `ager-…-interp-to-compiler-vm`): the CPS/defunctionalize route to deriving a VM from an interpreter — relevant to how `unwindFind`'s stack-search is structured (garby §6's "recursion operators, not explicit induction" hint).

**Strategic note (NOT a v1 fork):** `evalD` is **stateful-CK** (store-passing), not choice-tree-based. v1 = re-calculate the existing CalcVM cap-keyed (below). Re-grounding `evalD` in codensity choice trees is the SOTA-principled basis for the handler-compiler-calculation but a *re-architecture* of a 4320-line module — **post-v1** escape hatch, not a v1 detour.

## 2. The gated scope (build-arbitrated by ke-calcvm-scope @ `ef71972`, manager-gated)

**⚠ route-B is BIGGER than ADR-0052's "re-key `dispatch K ℓ op` → cap-keyed" framing.** Three confirmed findings:

- **(a) It's a signature-level `evalD` re-derivation + a ~1820-line BRIDGE rebuild.** `evalD` must thread the fresh-id counter `g`, MINT+substitute `vcap g h.label` at `handle` (reproducing the kernel's global-fresh ids in order, Operational.lean:471), and re-key `SStore`/`THeap` from **label ℓ → identity n**. Its type grows: `fuel → g → SStore → THeap → Comp → Option (Outcome × g' × SStore × THeap)`. That ripples through every lemma. The **bridge** (CalcVM.lean ~2483–4303: `dispatchRun`/`ctxStates`/`ctxTxns`/`CtxCorr`/`updateCtx*`/`run_evalD`/`evalD_agrees_source`) is keyed entirely to the OLD kernel (69× old 1-arg `handleF (.state…)`, 58× `Config.run` on pair configs, 27× label-dynamic `.perform 0 ℓ op v`) and must be re-derived. **GATED:** `lake build Bang.CalcVM` halts at line **2383** (143 errors) — the bridge (>2483) is *past the halt*, so its breakage is invisible to the error count. inc-6 ≫ "143 errors."
- **(b) "whole-tree green" needs inc-5 AND inc-7, not inc-6 alone.** Module status (build-confirmed): `Metatheory`/`LR`/`Model` ✓; `CalcVM` ~143 (inc-6); **`Compat` 40 own-errors — only 1 mentions vcap/CalcVM, the rest are LR/Config-triple re-index = inc-5**; `Compile` 0 own (CalcVM-blocked + latent); `Surface` (inc-7); `Audit` blocked on CalcVM+Compat+Surface; **`Spec` is transitive — greens only when inc-6 AND inc-5 (Compat) both land.** ⟹ **the ADR-0063 `type_safety` Spec re-point has a Compat (inc-5) dependency**, not just CalcVM.
- **(c) ADR-0058 (Canonical wall, task #33) is an inc-5 (Compat/LR) concern, NOT inc-6** — Compat's errors are LR-relation re-index, no CalcVM/vcap deref. Re-scope #33 onto the inc-5 track. (ADR-0058 file is also still phantom — backfill like 0056/0057/0060/0061 were.)

**Kernel template to mirror (green, axiom-clean):** `splitAtId K n` (Operational.lean:284, search by identity), `idDispatch` (:374 = `splitAtId.bind` + fail-loud `handlesOp h ℓ op` guard + `dispatchOn n op v`), `Source.step` perform arm (:485) + handle-mint (:471). `evalD`'s label-keyed store = the kernel's `state`/`transaction` frames projected; route-B re-projects them **by identity**.

## 3. Unit decomposition (leaf-first: fix `evalD` shape FIRST, everything downstream)

**Transfer-vs-recalculate ledger (build-attributed by case, ke-calcvm-scope).** Visible window ≈ **70 TRANSFER : 25 RECALCULATE (≈3:1 by sweep volume)** — but this measures *sweep volume*, NOT where the sessions go: the ~25 dispatch errors carry the entire novel derivation **plus the invisible ~1820-line bridge (dominantly recalculate)**. So: **by line-count mostly transfer (cheap); by effort/risk mostly recalculate.** The precise boundary, by Code constructor:
- **TRANSFER (dispatch-agnostic, Code falls out UNCHANGED — garby effect-independence):** `{RET, LAMI, SUBST, APP, CASE, SPLIT}` + UNFOLD-erasure. Cases `force`/`ret`/`lam`/`case`/`split`/`unfold` (~70 errors = vacuous `vcap` arms + AST re-key). → **U1**.
- **RECALCULATE (the novel handler-dispatch Code, re-derived IDENTITY-keyed from the cap-keyed `evalD` spec):** `{MARK, UNMARK, THROW, OP}` + `unwindFind`/`stateUpdate`/`txnUpdate` (CalcVM.lean:291–375). Today LABEL-keyed (`OP ℓ op v`, `unwindFind` searches by label); route-B → `OP` carries `n` / resolves via a `splitAtId`-analog over `HStack`, searches by **identity**. The kernel's green `idDispatch`/`splitAtId` is the spec these must satisfy. → **U2 + U3** (+ the bridge's `CtxCorr`/`dispatchRun`/`run_evalD` perform-handle arms).

 The 2 def parse-lines (`evalD`:213, `compile`:341, `.perform _ ℓ` → `.perform (.vcap _ ℓ)`) + ~8 vacuous `vcap` cases + perform-arity match patterns + the `Agree` battery (:2371–2385, 3 `rfl` + `OfNat Val 0`). Gate: CalcVM builds; `evalD_agrees_source` still FALSE on shadow (expected). Size **S**, risk low. (Boundary: defs parse + vacuous arms close; label-reasoning proof bodies still error until U2.)
- **U2 — re-derive `evalD` identity-keyed (the SEMANTIC CORE).** Thread `g`, mint+subst `vcap` at handle, re-key store label→identity, perform dispatches by `n` via the `splitAtId`-analog. Re-prove `sim` + `compile_correct` + `Agree`. Gate: `#print axioms compile_correct ⊆ {propext,Classical.choice,Quot.sound}`. Size **L** (multi-session). **Refute-risk:** return-only/vacuous handlers (`handle (throws 0)(ret 7)`) must survive (ADR-0052 flag — identity-keyed store must pop cleanly when the body never performs); the state/txn RESUME (shape-A) must re-key without losing op-disjointness.
- **U3 — re-derive the BRIDGE + `evalD_agrees_source` TRUE on shadow.** Rebuild `dispatchRun`/`ctxStates`/`CtxCorr`/`run_evalD` against the Config-triple + identity frames; close `evalD_agrees_source` on the ADR-0052 witness (`handle(state 1 10)(handle(state 1 20)(perform cap 1 "get"))` → 10 from BOTH). Gate: axiom-clean + a shadow-witness `#guard`. Size **L**. **⚠ THE WALL-RISK:** if the identity-keyed `evalD` can't be made to agree with `Config.run` over a clean `Corr` invariant, route-B breaks *here*. → The value-agreement de-risk is **DONE green** (§4). The NEXT refute-first rung, before the full-fuel proof: **prototype the step-wise `Corr`-lockstep invariant on the §2b put/get-inner witness** (`evalD'`'s identity-store ≡ kernel frame-projection at *every* step, not just the final value) — that's where the wall, if any, shows. Then the general `evalD_agrees_source`.
- **U4 — unblock Compile + the Spec/Audit re-point + the confluence.** Compile (`wexec ≈ exec`) re-closes once `compile_correct`/`evalD_agrees_source` statements settle (latent own-breakage — its sim composes the bridge theorems). Then the **ADR-0063 Spec re-point**: swap `HasConfig→HasConfig'`, `progress` onto the 3-disjunct form (Spec.lean:100), re-point `type_safety` at the banked axiom-clean `type_safety'_proof`/`progress'_proof` (`ef71972`). Size **M**. **Sequencing:** Spec also needs Compat (inc-5) green; Audit also needs Surface (inc-7) green — coordinate the three-increment confluence.

## 4. Refute-first de-risk — DONE, GREEN to the top cheap rung (2026-06-28, `scratch/RouteBShadowProbe.lean` @ `b7bbdc3`, manager-gated)

A minimal cap-keyed `evalD'` over the REAL AST, run on the ADR-0052 witness + escalations. `evalD'` (identity-keyed, mirrors `idDispatch`/`splitAtId`, mint+subst `vcap g h.label` at handle threading `g`) vs `evalDold` (label/nearest, byte-identical EXCEPT the store key) vs `Source.eval` (kernel oracle). **All ≡ kernel** (~20 `#guards`, EXIT 0):

| case | result | what it de-risks |
|---|---|---|
| §1 GET shadow | evalD'=10 ≡ kernel ≠ old=20 | the original ADR-0052 divergence |
| §2a PUT;GET outer | evalD'=99 ≡ kernel | mutation THREADS to the cap-named cell |
| **§2b PUT@outer;GET@inner** | evalD'=20 ≡ kernel ≠ old=99 | **identity-keyed mutation LANDS on the cap's cell, not nearest — the σ-update the get-only spike couldn't reach** |
| §3a/b return-only throws/state | evalD'=7 ≡ kernel | vacuous frame pops cleanly — the ADR-0052 retained-feature risk (C-new would have killed it) |
| §4a/b two-labels / throws-over-state | ≡ kernel | heterogeneous + interleaved frame coherence |

**Verdict: route-B's whole SEMANTIC core is build-confirmed sound** (the dispatch re-derivation + identity-keyed mutation compute the kernel's answers). **No semantic wall found.** What REMAINS is the **PROOF, not the semantics**: the step-wise **Corr-lockstep invariant** (`evalD`'s identity-store ≡ the kernel's frame-projection at *every* step — the ~1820-line bridge, `CtxCorr`/`run_evalD`) and full-fuel `evalD_agrees_source` over arbitrary programs. The spike confirms the answers; **U3 grinds the bridge proof.** Value-agreement is necessary, not sufficient — but the cheapest refutations all came back green, so the multi-session U1→U2→U3 commission is well-founded (awaiting operator go).
