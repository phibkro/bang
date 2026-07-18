<!-- note-status: active -->
# OS-inspiration survey — what operating systems teach bang about resources, scheduling, and access policy

> Research lane **ros** (2026-07-10). DOCS-ONLY. The operator's question: *what can operating
> systems teach a language/compiler/engine about managing memory, compute, and security/access
> policy over actors/processes?* This note prices every OS idea against **what bang already
> has** — it is a decision-shaped set of ADR-INPUTS, not a book report. Nothing here is scoped
> v1 work; the verdict + input ledger are at the bottom (§9, §10).
>
> Sibling adjacent-field surveys: `rdbms` (task #23, compiler-as-DBMS) and the pending LSP lens.
> All three converge on one structural claim developed in §1: **bang's five primitives are a
> microkernel; the language/tooling/runtime are userland.** The honest verdict on whether that
> framing is load-bearing or rhetoric is in §1.

---

## 0 · TL;DR (the verdict, up front)

```
the load-bearing frame : bang's 5 kernel primitives (thunk·force·rows·handlers·STM) ARE a
                         microkernel; surface/runtime/stdlib are userland. LOAD-BEARING, not
                         rhetoric — it PREDICTS four already-made decisions (§1) and one open one.

cheapest actionable    : ROW ATTENUATION — `pledge {E, …} in body`, a checked effect-row ceiling.
                         LANDED as ADR-0112. The distinct value-policy half is now executable too:
                         ADR-0113 carries a runtime host allowlist in an ordinary handler. §4, §10.

the future headline    : seL4's NONINTERFERENCE theorem is the exact shape of bang's future
                         security headline — "effects cannot flow where the row forbids." bang's
                         two-hop (§1) IS seL4's refinement chain; the row IS the access-control
                         policy. POST-V1, research-grade, but the architecture already fits. §2.

post-v1, not research   : Erlang supervision → handler-scope restart/propagate policy (§6);
                         Midori abandonment → escapedCap generalized to a fail-loud domain (§3).

rejected / deferred     : hand-designed scheduler primitive (fuel already IS the quantum, §5);
                         hardware isolation (bang is SOFTWARE-isolated by types, Singularity's
                         bet, §3); region memory as a KERNEL feature (it's a grade, §7).
```

---

## 1 · The structural claim: five primitives are a microkernel

The operator's three adjacent-field questions — LSP, DBMS, OS — converge here. The claim to test:

```
  MICROKERNEL (privileged, proven, frozen)        USERLAND (unprivileged, tested, replaceable)
  ────────────────────────────────────────        ───────────────────────────────────────────
  thunk · force · effect-rows · handlers · STM     surface syntax · elaborator · checker
  (5 primitives, invariant #5)                     runtimes (= handlers at the use site)
                                                   stdlib (prelude, user handlers, CRDTs)
  the calculated VM + WasmFX target                bang query / LSP / formatter / bang test
```

**Is this load-bearing or rhetoric?** The test of a mental model is whether it *predicts design
decisions* you'd otherwise have to argue case-by-case. Four landed decisions fall out of the
microkernel frame as *theorems*, not coincidences:

1. **"STM is the only privileged primitive; everything else is effect + handler"** (invariant #3,
   ADR-0030) is *exactly* the microkernel minimality principle: **mechanism in the kernel, policy
   in userland.** seL4 puts scheduling *mechanism* (context-switch) in the kernel but scheduling
   *policy* (which thread next) in a userland server. bang puts effect *mechanism* (perform/handle
   dispatch) in the kernel and effect *policy* (what a handler DOES — state, txn, IO, retry) in
   userland handlers. The Liedtke minimality principle — *"a concept is tolerated inside the
   microkernel only if moving it outside would prevent the implementation of the system's required
   functionality"* — is *the same sentence* as bang's invariant #5 ("adding a sixth primitive is a
   spec change requiring an ADR"). This is not an analogy; it is the same constraint.

2. **"Runtime is a handler installed at the use site"** (the moat thesis) is the microkernel's
   *userland server* model. In seL4/L4, the "OS" is a set of userland servers you install; the
   kernel just routes IPC. In bang, the "runtime" is a set of handlers you install; the kernel just
   routes `perform`. **ADR-0093 D5 makes this literal**: `main`'s effect row is the *capability
   manifest*, and `bang run` is the use site that installs handlers for exactly that row — the CLI
   contract IS "userland requests these kernel services; the loader provides them or fails loud."

3. **Per-identity stores + id-first dispatch** (Stage 4, AbstractMachine.lean) is *address-space
   isolation by construction*. Each `handle` mints a generative-fresh identity `n` and owns a store
   keyed by `n`; the three stores are disjoint by freshness — this is precisely a microkernel's
   *"each process gets its own address space, named by an unforgeable id."* The vcap's identity `n`
   is a **handle** in the Fuchsia/KeyKOS sense (§4): an unforgeable reference to one kernel object.

4. **The escaped-capability fail-loud** (`escapedCap`, ADR-0063) is the microkernel's *fault on an
   invalid capability*. Dispatch a cap after its handler popped → the kernel has no frame for
   identity `n` → defined fail-loud terminal, never silent. seL4 faults on an invalid CSpace slot;
   bang returns `escapedCap`. Same move (§3).

**One decision it PREDICTS but hasn't been made:** if the frame is real, *row-attenuation is the
`seccomp`/`pledge` of this microkernel* — a userland process voluntarily dropping its own kernel
privileges, irreversibly, to sandbox code it calls. That combinator does not exist yet (§4, §9),
and the frame says it *should* and says *where it goes* (a userland row-narrowing operator, not a
kernel primitive). A frame that predicts an unbuilt feature and its placement is load-bearing.

**Honest limit of the frame.** It is load-bearing for *structure* (what is privileged, where policy
lives, how isolation is named) but says *nothing* about the two things a real microkernel spends its
life on: **scheduling fairness** and **IPC performance**. bang's fuel (§5) is a *degenerate*
scheduler (one computation, cooperative, no fairness). Real preemptive multi-tenant scheduling is
post-v1 and the microkernel frame gives no free lunch there — it tells you scheduling is a userland
*policy* over a kernel *quantum*, which is the right shape, but the hard part (fairness, priority
inversion, gang scheduling) is unaddressed. Claiming the frame solves scheduling would be the
rhetoric failure. It solves *placement*, not *policy content*.

> **Verdict: LOAD-BEARING.** Keep the frame; it earns its place by predicting decisions 1–4 and
> the placement of row-attenuation. State its limit (scheduling policy content) honestly.
> This belongs in an ADR as the *organizing principle* behind invariants #3/#5, with seL4's
> Liedtke minimality as the cited prior art.

---

## 2 · seL4 — the verified capability microkernel (the future security headline)

seL4 is the lodestar: a general-purpose microkernel with machine-checked proofs of functional
correctness *and* security, capability-based throughout. Three pieces price directly against bang.

### 2.1 Refinement architecture ≅ bang's two-hop

seL4's proof is a **refinement chain**: an abstract security statement → an access-control model →
the abstract spec → an executable spec → the C implementation → the binary. A property proved at
the abstract level *transfers down* to the C code and binary by refinement [Klein13, Murray13].

This is **structurally bang's two-hop** (ADR-0016): `source → graded-CBPV semantics → CalcVM
(Bahr–Hutton) → WasmFX`. The kernel `Source.eval` is bang's abstract spec; `evalD`/the calculated
VM is the executable spec; the WasmFX backend is the C/binary analog, tied back by
`compile_forward_sim`. **bang already has the seL4 refinement skeleton** — the security theorem of
§2.2 would ride on top of it exactly as seL4's noninterference rides on its functional-correctness
refinement.

### 2.2 The noninterference theorem — the shape of bang's security headline

seL4 proves **intransitive noninterference**: verbatim, *"the kernel enforces this noninterference
policy... shows that the kernel allows no other information flows than those implied by the current
access control policy"* [Murray13, infoflow.pml]. Two properties precede it:

- **Authority confinement**: the authority distribution in future states never exceeds that implied
  by the current access-control policy.
- **Integrity**: the running thread cannot modify anything the policy disallows; **confidentiality**:
  it cannot read anything the policy disallows. Integrity + confidentiality give the *unwinding
  conditions* that discharge noninterference.

**The bang translation is direct and it is the future headline:**

```
  seL4                                    bang (post-v1)
  ────                                    ──────────────
  access-control policy (capabilities)    the effect ROW on main (ADR-0093 D5 manifest)
  security domain                         a handler identity / a labelled effect
  noninterference: no flow not implied    SOUNDNESS: no effect performed that the row forbids
    by the policy                           — "effects cannot flow where the row forbids"
  authority confinement                    row monotonicity + no-ambient-authority (the vcap must
                                            be NAMED to perform; §4)
  integrity/confidentiality unwinding      the no_accidental_handling obligation + type_safety
```

bang's `no_accidental_handling` soundness obligation is *already* an authority-confinement lemma in
miniature: a `perform` can only reach a handler its capability names. Generalized to an
information-flow *lattice as a grade axis* (§8, laws-taxonomy §5 — "an IFC lattice is a grade
axis"), the row becomes a security policy and soundness becomes noninterference.

### 2.3 The caveats bang inherits (state them or overclaim)

seL4's noninterference is not free and its assumptions are exactly the ones bang must not paper over:

- **Deterministic scheduler required.** The original seL4 scheduler *leaked via its scheduling
  decisions*; the proof only holds for a modified fixed-partition scheduler. **Lesson for bang:**
  the moment scheduling becomes a shared handler over multiple tenants (§6), the scheduler is inside
  the TCB for any information-flow claim. Fuel today is deterministic (§5) — keep it so.
- **Static configuration.** The policy is a fixed input; dynamic reconfiguration is out of scope.
  bang's row is static (typed) — this *favors* bang: the manifest is a compile-time fact.
- **Timing/microarchitectural channels excluded.** seL4 needed a *separate* line of work
  [arXiv:2310.17046] for timing channels. **bang must state the same exclusion**: a row-as-policy
  theorem bounds *semantic* flows, not wall-clock/cache side channels.

> **ADR-INPUT.** The noninterference theorem is bang's *◊-far* security headline, and its
> architecture (refinement chain + capability policy) is ALREADY IN PLACE via the two-hop and the
> vcap. The publishable path: (1) an IFC grade axis (§8), (2) a `row-forbids ⇒ never-performed`
> theorem over the total fragment, (3) the honest timing-channel exclusion. This is post-v1 and
> research-grade, but it is *not* speculative — it is the seL4 result ported to an effect row.

---

## 3 · Singularity / Midori — software isolation and the error model

### 3.1 SIPs: isolation by types, not hardware — bang is already here

Singularity's three pillars [Hunt07]: **software-isolated processes** (SIPs), **contract-based
channels**, **manifest-based programs**. The load-bearing bet: *"SIPs are isolated by software
verification instead of hardware protection, and thus rely on programming-language type and memory
safety for isolation."* SIPs cannot share memory; they communicate over typed channels; isolation
costs far less than a hardware context switch.

**bang has already placed Singularity's bet.** bang's isolation is *type-and-identity* based
(per-identity stores, §1 decision 3), not hardware. This is the *entire* justification for the
microkernel-in-a-language frame: you get address-space-style isolation *without* an MMU because the
type system + generative identities make cross-domain access unrepresentable. The three pillars map:

```
  Singularity            bang
  ───────────            ────
  SIP (type-isolated)    a handler instance + its per-identity store
  contract channel       the effect signature (op-set + arg/result types the handler honors)
  manifest program       main's row (ADR-0093 D5) — the checked manifest of required capabilities
```

The **manifest** parallel is the sharpest: Singularity refused to run a program whose manifest
couldn't be satisfied; ADR-0093 D5 makes `bang run` refuse (loud type error, post-v1) a program
whose `main` row the runtime can't provide handlers for. *Same contract.*

### 3.2 Midori's error model — abandonment IS escapedCap, generalized

Joe Duffy's Midori retrospective [Duffy16] is required reading for bang's actor/error design. The
model is **two-pronged**:

- **Abandonment (fail-fast)** for *bugs* — null deref, bounds, overflow, contract violation. *"tore
  down the entire process in an instant, refusing to run any user code while doing so."*
- **Statically-checked exceptions** for *recoverable* errors — I/O, timeout, parse. Rare: *"90-
  something% of the typical uses of exceptions in .NET/Java became preconditions."*

**The load-bearing coupling for bang:** *"None of the language features... would have worked so well
without this architectural foundation of cheap and ever-present isolation."* Abandonment is only
safe because a torn-down SIP corrupts nothing else. **This is exactly bang's `escapedCap`**
(ADR-0063): a defined fail-loud terminal, *no user code runs on the way out*, safe precisely because
the per-identity store isolation (§1.3) means the abandoned computation corrupted nothing shared.

```
  Midori                          bang (landed)                     bang (post-v1 generalization)
  ──────                          ─────────────                     ─────────────────────────────
  abandonment (bug → tear down)   escapedCap terminal (ADR-0063)    per-actor abandonment domain
  checked exceptions (recover)    throws handler (ADR-0023)         (unchanged)
  cheap isolation makes it safe   per-identity stores (Stage 4)     per-actor stores
  contract pre/postconditions     (not yet — see below)             refinement-typed handler laws
```

**The retrospective regrets bang should bank now:** Duffy's *"biggest regret is that we waited so
long on non-null types"* — the meta-lesson is *make the bad state unrepresentable at the type level
early, don't bolt on runtime contracts later*. This is literally bang's correctness-by-construction
root. bang's advantage: `escapedCap` is *already* a defined terminal, not a bolted-on check — bang
is doing at v1 what Midori wished it had done from the start. **The actor-design input:** when `!`
actor-send lands (post-v1, ADR-0030 reserved), each actor is an abandonment domain; a bug abandons
*one* actor (fail-loud escapedCap-style), and *supervision* (§6) decides restart-vs-propagate. Midori
+ Erlang together give the whole actor error story: abandonment is the *mechanism*, supervision is
the *policy* — again microkernel-shaped (§1).

> **ADR-INPUT.** Adopt Midori's bug/recoverable split explicitly as the bang error taxonomy:
> `escapedCap`/contract-failure = abandonment (fail-loud, already landed); `throws` = recoverable
> (already landed). The generalization to per-actor abandonment domains is post-v1 but the terminal
> and the isolation it rides on are BOTH already in place.

---

## 4 · Capability discipline + pledge/unveil ⇒ ROW-ATTENUATION (the cheapest actionable item)

### 4.1 The capability-security canon, priced against the vcap

The KeyKOS→EROS→Capsicum→CHERI→Fuchsia lineage shares one principle: **no ambient authority.**
*"The only access logic in capability systems is 'does the process have the capability'; there is no
ambient authority and thus no global namespace... no confused-deputy problem"* [CapMyths, Miller03].
A **handle** (Fuchsia) / **capability** (CHERI) is an *unforgeable reference* to one object; authority
is *possession*, not identity-in-an-ACL.

**bang's vcap is a capability in exactly this sense:** `vcap n ℓ` is unforgeable (identity `n` is
generative-fresh, ADR-0055), and a `perform` *must name* its cap — there is **no ambient authority**;
you cannot perform an effect you don't hold a cap for. bang therefore inherits the canon's headline
property *for free*: **no confused deputy.** A handler cannot be tricked into exercising an authority
it wasn't handed, because dispatch is identity-keyed (§1.3) — the deputy can only reach the handler
its cap names, never a caller's ambient one.

The two hard problems the canon flags:

- **Revocation** — CHERI's expensive problem: capabilities *copy freely*, so revoking one means
  finding all copies. **bang's one-shot resumption is a revocation primitive**: a linear/affine
  capability that can be exercised *once* is self-revoking (the confused-deputy window closes after
  first use). The multishot-survey (Q22) is where this is decided; **affine caps = cheap revocation**
  is an input to that.
- **Attenuation** — seL4's CDT (capability derivation tree): a derived cap carries *≤* the authority
  of its parent; `revoke` removes the whole subtree. This is the model for §4.2.

### 4.2 pledge/unveil ⇒ first-class ROW-ATTENUATION combinators

OpenBSD `pledge(2)` requests a *subset* of syscalls via named promises (`stdio`, `rpath`, `inet`,
`dns`, ...); `unveil(2)` restricts filesystem paths. Two properties are the design gift:

1. **Named coarse subsets**, not fine-grained BPF — *"the loss in granularity is a cheap price for
   simplicity."* pledge beat seccomp on *ergonomics*.
2. **Irreversible** — pledge sets `NO_NEW_PRIVS`; you can drop authority but never regain it.

**Landed as ADR-0112 (2026-07-18).** The sandboxed-plugin example
(`docs/spec/bang-lang-design.md`) needed a row-only way to state the plugin's complete effect ceiling.
Bang now spells that checked boundary `pledge {E, …} in body`; the original survey finding is
retained here as the evidence that selected the slice, not as a current limitation.

**Row-attenuation combinator** = pledge, made a type:

```
  c : A with ρ      ρ ⊑ ρmax
  ─────────────────────────────────────────────────────────────────────
  pledge ρmax in c : A with ρ   -- retains the ACTUAL row; a wider perform is a TYPE ERROR
```

Why this is **v1.x-cheap** (the cheapest actionable item):

- **No new kernel primitive.** Attenuation is a *checked upper bound* on the row a sub-computation
  may carry — it rides the row lattice bang *already has* (`[Lattice Eff] [OrderBot Eff]`, invariant
  #2, ADR-0018). `⊑` is already defined. Invariant #5 (five primitives) is untouched.
- **No proof budget.** It is a typing rule (elaborator + checker), the *tested* superset — the
  language-level seam, not the verified kernel. It's a `pledge`-shaped restriction expressed as
  row-subtyping, which the checker already reasons about.
- **It unlocks the flagship showcase.** `examples/pledged-plugin/` is the executable witness: an
  Audit-only plugin type-checks, while adding a `Secret` perform fails at compile time.
- **It is the userland `seccomp` the microkernel frame predicted** (§1): a userland computation
  voluntarily, irreversibly narrowing its own kernel privileges before calling untrusted code.

**Honest wall.** Attenuation narrows the *static* row (what the code is *typed* to perform). It does
NOT by itself narrow *values inside* an effect — `allowed_paths=["/var/data"]` is a *value*
restriction (which path), not a *row* restriction (whether IO at all). Full path-level unveil needs
either (a) a refinement/dependent type on the IO cap's argument, or (b) the handler itself enforcing
the whitelist at runtime (a userland *policy handler*, which bang can already write). **Recommended
split:** row-attenuation (the `pledge` half — *whether* the effect) is the cheap type-level v1.x win;
value-level unveil (the *which resource* half) is a handler-enforced policy today, a refinement type
post-v1. `examples/policy-host-allowlist/` now confirms this route with one unchanged plugin under
two runtime handler parameters (ADR-0113). Don't conflate them — pledge and unveil are *two*
syscalls for a reason.

> **ADR-INPUT — EXECUTED by ADR-0112.** Bang shipped row attenuation as
> `pledge {E, …} in body`: a row-subtyping rule in the checker, no kernel change. The actual row is
> retained after the assertion. ADR-0113 separately confirms value-level policy as runtime handler
> configuration, still outside the row assertion itself.

---

## 5 · Scheduling: fuel is already the quantum — do NOT add a scheduler primitive

OS scheduling = a *quantum* (preemption granularity) + a *policy* (who runs next). bang already has
the quantum: **fuel** bounds `Source.eval` (`Config.run`, Eval.lean), decrementing per `Source.step`;
exhaustion → `.outOfFuel`. This is *cooperative-preemption's time-slice*, and the Div fragment (fuel-bounded)
vs total fragment (⊥-row) split is the language-level stratification seam (CLAUDE.md).

**The input is a non-action:** do **not** hand-design a scheduler primitive. Per the microkernel
frame (§1) and invariant #7 (performance is second-class), scheduling is a *userland policy over the
existing quantum*:

- The quantum (fuel) is kernel mechanism — landed, deterministic (which §2.3 says to *keep* for any
  future noninterference claim).
- Multi-tenant scheduling *policy* (fairness, priority) is a **handler** — `handlers-as-schedulers`
  (distributed-story.md): a scheduler handler owns nondeterminism/interleaving, which is exactly
  FoundationDB-style deterministic-simulation testing as library code.

**The honest wall (restated from §1):** the microkernel frame gives *placement* (quantum in kernel,
policy in a handler) but not *policy content*. Fairness, priority inversion, and gang scheduling are
genuinely hard and genuinely post-v1 (they need multi-shot resumption, Q22, + concurrency, ADR-0030).
Fuel-as-quantum is a *cooperative single-computation* scheduler — adequate for v1, honestly
inadequate for multi-tenant preemption. That's a post-v1 handler, not a kernel gap.

> **ADR-INPUT.** Scheduling needs NO kernel work. Fuel is the quantum; the scheduler is a post-v1
> handler over it (distributed-story rung 2). Bank "keep fuel deterministic" as a *constraint* the
> future noninterference theorem (§2.3) depends on.

---

## 6 · Erlang/OTP supervision ⇒ handler-scope restart/propagate policy

Erlang's **"let it crash"** + **supervision trees**: a process that hits a bad state *crashes*
(no defensive programming); a **supervisor** restarts it in a clean state per a strategy
(`one_for_one`: restart only the failed child; `one_for_all`: restart siblings; `rest_for_one`).
Supervision trees are *fault-isolation boundaries* — a crashed worker doesn't cascade [AdoptingErlang].

This is the **policy** half of the actor error story whose **mechanism** half is Midori abandonment
(§3.2). The parallel to bang is precise and it lands on *handler scope*:

```
  Erlang/OTP                         bang (post-v1, actor design)
  ──────────                         ────────────────────────────
  process crash ("let it crash")     escapedCap / contract-fail abandonment (§3.2, landed terminal)
  supervisor                         a SUPERVISION HANDLER installed above the actor
  restart strategy (one_for_one…)    the handler's policy: on child abandonment, restart | propagate
  supervision tree = fault boundary  handler nesting = the fault boundary (per-identity isolation §1.3)
  clean restart clears transient     restart = re-install the handler with a fresh identity/store
```

The insight bang gets *for free*: **the handler-installation nesting IS the supervision tree.** A
handler already delimits a dynamic extent and owns an isolated per-identity store; making it a
supervisor is *adding a restart/propagate policy to its abandonment arm*, not new structure. "Restart
in a clean state" = re-install with a fresh generative identity (a new store, §1.3). `one_for_one`
vs `one_for_all` becomes *which sibling handlers the supervisor re-installs* on a child's escapedCap.

> **ADR-INPUT.** Supervision is a **post-v1 handler policy**, not a primitive: an abandonment-arm
> restart/propagate strategy on a handler that scopes actors. It needs actors (`!`, ADR-0030
> reserved) + multi-shot resumption (Q22) first. The *mechanism* (abandonment terminal, isolated
> stores) is landed; only the *policy layer* is missing. Handler nesting = supervision tree is the
> free structural win.

---

## 7 · Memory: regions ⇒ a grade, not a kernel feature; intralingual ⇒ bang's whole thesis

### 7.1 MLKit regions ⇒ handler-scoped arenas licensed by a grade

MLKit pioneered **region inference**: the compiler infers, per allocation, the *youngest region whose
lifetime contains the value's*, and emits region create/free at compile time; regions form a *stack*
(r1 before r2 ⇒ r2 freed before r1) [Tofte98, MLton]. A region = an arena freed all-at-once.

The bang mapping: **a handler already delimits a stack-disciplined dynamic extent** (install…pop, LIFO,
exactly a region stack). So **handler-scoped arenas** are the natural home for region memory — a
handler owns an arena; values allocated under it die when it pops. But this is **not a kernel
primitive**; per the grade-axes ruling (laws-taxonomy §5), *lifetime/region is a candidate GRADE
AXIS*: an ordered algebra (region nesting is a lattice) folded along composition, admissible iff its
laws hold. Region memory becomes a *coeffect* the type system tracks, licensing arena allocation —
the same machinery as the IFC axis (§8) and the CALM monotonicity axis (calm-as-grade-survey),
*different lattice*.

### 7.2 Theseus / Rust / MirageOS — intralingual is bang's founding thesis, confirmed

Theseus's **intralingual** design [Boos20]: *"empowers the compiler to take over resource-management
duties, reducing the states the OS must maintain, which... strengthens isolation."* MirageOS
unikernels [Madhavapeddy13]: *the app IS the OS* — single address space, no process management, no
virtual memory; **types eliminate the layers** a conventional OS needs.

**This is bang's founding thesis, independently arrived at by the OS community.** bang's claim —
"paradigm and runtime are *values*, not language features; the kernel is 5 primitives and everything
else is library code" — is *intralingual resource management* verbatim: the compiler (type system +
rows) takes over what an OS runtime would track. The row-as-manifest (D5) eliminating a separate
capability-configuration layer is *exactly* MirageOS eliminating the OS/app boundary. **Corroboration,
not a new feature:** the OS literature validates that the intralingual bet *works* (Theseus/Mirage are
real systems), which de-risks bang's core wager.

> **ADR-INPUT.** Region memory is a **grade axis** (post-v1, laws-taxonomy §5 machinery), *not* a
> sixth primitive — handler scope is the region stack for free. Theseus/MirageOS are *citations that
> de-risk the intralingual thesis*, not features to build.

---

## 8 · The IFC lattice as a grade axis — the bridge from §2 to bang's existing machinery

The seL4 noninterference headline (§2) needs a *policy*: a lattice of security levels with a
permitted-flow order. bang already ruled how to get one: **laws-taxonomy §5 — "an IFC lattice is a
grade axis."** A user declares a security lattice `[Lattice L]` (e.g. `Public ⊑ Secret`), annotates
leaf ops with levels, and the *generic* `GradeVec` propagation folds it along composition — the same
mechanism that carries rows (the effect lattice), multiplicity (0/1/ω), and monotonicity (CALM). The
admissibility gate is the law machinery (`lawInstancesOf` + `bang test` fuzz + Q43 total-fragment
proof): an axis is admissible iff its algebra's laws (assoc/comm/idem/monotone-join) hold.

**So the path from bang-today to the seL4-shaped headline is short and reuses landed machinery:**

```
  landed: rows are join-semilattices (invariant #2) + grade axes are user-definable (laws-tax §5)
     │
     ├─ declare an IFC lattice as a grade axis            ← reuses GradeVec, zero new primitive
     ├─ row-attenuation (§4) restricts the axis           ← the pledge/drop-to combinator
     └─ prove "level-forbidden ⇒ never-flows" (total)     ← the §2 noninterference theorem, in miniature
```

Granule (security lattices as grades) and F# units-of-measure (user abelian group, type-level fold,
zero semantic proof) are the shipped precedents laws-taxonomy §5 already cites. **bang's structural
advantage** (same as CALM, calm-as-grade-survey §0): it is *already* graded CBPV with lattice rows;
the IFC axis is a *reuse*, not a new subsystem. Everyone else bolts IFC on; bang folds it into
machinery it paid for once.

---

## 9 · The honest walls (what this survey does NOT solve)

```
  wall                                   why it's hard                          disposition
  ────                                   ─────────────                          ───────────
  timing / cache side channels           semantic rows bound MEANING flows,     state as EXCLUSION in
                                          not wall-clock; seL4 needed a          any noninterference
                                          separate proof line                    claim (§2.3). NOT solved.
  multi-tenant scheduling fairness       needs multi-shot (Q22) + concurrency    post-v1 handler; frame
                                          (ADR-0030); priority inversion etc.    gives placement not policy
  value-level unveil (which resource)    runtime policy handler works today;     host allowlist landed;
                                          static proof needs refinements           refinements remain post-v1 (§4)
  the noninterference theorem itself     seL4-scale proof effort; needs the      research-grade, post-v1;
                                          IFC axis + total-fragment discipline    architecture IS in place
  actors (`!`) + supervision             reserved (ADR-0030), needs multi-shot   post-v1; mechanism landed,
                                          resumption + concurrency runtime        policy layer missing (§6)
  CHERI-style free-copy revocation       caps copy freely → find-all-copies      affine/one-shot caps make
                                          is the expensive case                   it cheap; input to Q22 (§4.1)
```

The frame (§1) is honest about its own limit: it solves *placement* (what's privileged, where policy
lives), not *policy content* (fairness algorithms, timing mitigation). Overclaiming that "bang is a
verified OS" would be the rhetoric failure the operator asked to guard against — bang is a language
whose *structure* is microkernel-shaped, which predicts decisions and de-risks a security headline,
which is a strong and *true* claim, and a different one from "solved."

---

## 10 · ADR-INPUTS — the decision ledger

Cost-tiered, per the task's ask (v1.x-cheap / post-v1 / research):

| # | input | tier | rides on / cost | ADR home |
|---|-------|------|-----------------|----------|
| **I1** | **Row attenuation** (`pledge {E, …} in body`): pledge-as-a-type; checked row upper bound retaining the actual row. **LANDED 2026-07-18.** | **v1.x — shipped** | existing row lattice (inv #2); typing rule only, no kernel change | [ADR-0112](../decisions/0112-row-attenuation-as-erased-pledge.md) + `examples/pledged-plugin/` |
| **I1b** | **Value-level resource policy as handler configuration**: runtime allowlist values are carried through `(Effect init)` / `param`, separate from the row. **LANDED 2026-07-18.** | **v1.x — shipped** | existing parameterized custom handlers + first-class installers; no kernel change | [ADR-0113](../decisions/0113-value-level-resource-policy-is-handler-configuration.md) + `examples/policy-host-allowlist/` |
| **I2** | **Microkernel/userland as the organizing principle** behind invariants #3/#5, citing Liedtke minimality + seL4. LOAD-BEARING (predicts 4 landed decisions + I1's placement). | **v1 (doc)** | pure framing; no code | NEW ADR (principle) or a §in CLAUDE.md's architecture |
| **I3** | **Midori bug/recoverable error taxonomy** made explicit: escapedCap/contract = abandonment (landed), throws = recoverable (landed). | **v1 (doc)** | both terminals already landed | amend ADR-0063 (escape) with the taxonomy |
| **I4** | **IFC lattice as a grade axis** — the policy substrate for I5. Reuses GradeVec (laws-tax §5). | **post-v1** | grade-axis machinery (post-v1 surface); no new primitive | laws-taxonomy §5 → future ADR when axes ship |
| **I5** | **Row-forbids ⇒ never-performed** (noninterference, total fragment) — bang's security headline; seL4 result ported to the row. Needs I4 + honest timing-channel exclusion. | **research** | two-hop refinement (landed) + I4 + total-fragment discipline | future ADR; ◊-far |
| **I6** | **Supervision = handler restart/propagate policy** on the abandonment arm; handler nesting = supervision tree. | **post-v1** | actors (`!`, ADR-0030 reserved) + multi-shot (Q22) | future actor ADR |
| **I7** | **Affine/one-shot caps = cheap revocation** (vs CHERI free-copy). | **post-v1** | input to the multishot decision | Q22 / multishot-survey |
| **I8** | **Region memory = a grade axis**, handler scope = region stack. NOT a sixth primitive. | **post-v1** | grade-axis machinery (laws-tax §5) | future ADR |
| **I9** | **Keep fuel deterministic** — a *constraint* the future noninterference theorem (I5) depends on (seL4's scheduler-leak lesson). No scheduler primitive. | **v1 (constraint)** | fuel already landed + deterministic | note on ADR-0030 / the I5 ADR |

**The one-line recommendation (executed):** I1 was the single v1.x-cheap surface form that unlocked
the sandboxed-plugin showcase and gave bang the capability-security canon's headline pair (no
ambient authority + attenuation) with zero kernel
or proof cost, and is the concrete first down-payment on the seL4-shaped noninterference headline (I5)
that the microkernel frame (I2) says bang is architecturally positioned to reach.

---

## References

Cited inline by [key]. All are primary sources or their canonical summaries.

- **[Klein13]** Klein et al., *Comprehensive Formal Verification of an OS Microkernel*, ACM TOCS
  2013. The seL4 refinement architecture (abstract spec → C → binary). <https://sel4.systems/Verification/proofs.html>
- **[Murray13]** Murray et al., *seL4: from General Purpose to a Proof of Information Flow
  Enforcement*, IEEE S&P 2013. The (intransitive) noninterference theorem.
  <https://sel4.systems/Research/pdfs/sel4-from-general-purpose-to-proof-information-flow-enforcement.pdf>
- **[infoflow.pml]** Trustworthy Systems, *Information Flow* project page (noninterference statement +
  scheduler/timing caveats). <https://trustworthy.systems/projects/OLD/infoflow.pml>
- **[arXiv:2310.17046]** *Proving the Absence of Microarchitectural Timing Channels* — the separate
  timing-channel line seL4 needed. <https://arxiv.org/pdf/2310.17046>
- **[seL4-manual]** *seL4 Reference Manual* — capability derivation tree (CDT), untyped-memory retype,
  revoke. <https://sel4.systems/Info/Docs/seL4-manual-latest.pdf>
- **[Hunt07]** Hunt & Larus, *Singularity: Rethinking the Software Stack*, OSR 2007. SIPs,
  contract-based channels, manifest-based programs.
  <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/osr2007_rethinkingsoftwarestack.pdf>
- **[Duffy16]** Joe Duffy, *The Error Model* (Midori retrospective), 2016. Abandonment vs checked
  exceptions; cheap-isolation coupling; non-null-types regret.
  <https://joeduffyblog.com/2016/02/07/the-error-model/>
- **[Miller03] / [CapMyths]** Miller, Yee, Shapiro, *Capability Myths Demolished*, 2003. No ambient
  authority ⇒ no confused deputy. <https://srl.cs.jhu.edu/pubs/SRL2003-02.pdf>
- **[Ambient]** *Ambient authority*, Wikipedia (confused-deputy framing).
  <https://en.wikipedia.org/wiki/Ambient_authority>
- **[Capsicum]** Watson et al., *Capsicum: practical capabilities for UNIX*, USENIX Security 2010
  (capability sandboxing on UNIX). <https://css.csail.mit.edu/6.858/2017/lec/l06-capsicum.txt>
- **[Fuchsia]** Fuchsia handles — unforgeable object references as capabilities.
  <https://fuchsia.dev/fuchsia-src/concepts/kernel/handles>
- **[pledge]** *pledge(2)*, OpenBSD manual (named promise subsets, irreversible).
  <https://man.openbsd.org/pledge.2>
- **[deRaadt16]** de Raadt, *Privilege Separation and Pledge*, 2016. <https://www.openbsd.org/papers/dot2016.pdf>
- **[AdoptingErlang]** *Supervision Trees*, Adopting Erlang (restart strategies, let-it-crash).
  <https://adoptingerlang.org/docs/development/supervision_trees/>
- **[Tofte98]** Tofte & Talpin, *A Region Inference Algorithm*, TOPLAS 1998.
  <https://elsman.com/mlkit/pdf/toplas98.pdf>
- **[MLton]** MLton, *Regions* (stack-of-regions, finite vs infinite). <http://mlton.org/Regions>
- **[Boos20]** Boos et al., *Theseus: an Experiment in OS Structure and State Management*, OSDI 2020.
  Intralingual design; compiler takes over resource management.
  <https://www.usenix.org/system/files/osdi20-boos.pdf>
- **[Madhavapeddy13]** Madhavapeddy et al., *Unikernels: Library Operating Systems for the Cloud*,
  ASPLOS 2013. MirageOS; types eliminate OS layers. <https://anil.recoil.org/papers/2013-asplos-mirage.pdf>
- **[Liedtke95]** Liedtke, *On µ-Kernel Construction*, SOSP 1995. The minimality principle.
  <https://os.inf.tu-dresden.de/pubs/sosp95/>

### bang-internal anchors (priced against)

- vcap identity+label + typing-by-label/dispatch-by-identity: `Bang/Core/IR.lean`,
  `Bang/Core/Semantics/Dispatch.lean`; ADR-0054, ADR-0055.
- escapedCap fail-loud terminal: `Bang/Core/Semantics/Eval.lean`; ADR-0063.
- main's row as capability manifest: ADR-0093 D5.
- per-identity stores + id-first dispatch: `Bang/Backend/AbstractMachine.lean`; ADR-0052, ADR-0085 Stage 4.
- fuel as quantum: `Bang/Core/Semantics/Eval.lean` (`Config.run`).
- handlers-as-schedulers: `docs/notes/distributed-story.md`.
- grade axes / "IFC lattice is a grade axis": `docs/notes/laws-taxonomy.md` §5.
- reserved `!` + STM privilege: ADR-0030; invariants #3, #5.
- CALM-as-grade (sibling axis): `docs/notes/calm-as-grade-survey.md`.
