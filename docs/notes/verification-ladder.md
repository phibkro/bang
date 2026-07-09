<!-- note-status: active -->
# The verification ladder — quality gates for agent-speed code

> Operator hypothesis (2026-07-09): as agents accelerate code output, quality gates become the
> binding constraint on correctness. The sharpening this note records: what matters is the
> gates' **latency ordering** — an agent's loop tightens around the fastest gate that can catch
> its current mistake-class, so the design goal is a ladder where each rung is as fast as its
> error-class allows. This is the agent-first lens ([[agent-first-ergonomics-lens]] in the
> operator's memory; the CLAUDE.md invariants) applied to VERIFICATION.

## The ladder (bang today + the build order)

| rung | catches | latency | status |
|---|---|---|---|
| types + effect rows | wrong shapes, undeclared effects — the paradigm IS the gate | ms | ✅ live |
| `bang check --json` | located, machine-readable diagnostics (#59) | ms | ✅ live |
| canonical `fmt` | style entropy (deleted, not reviewed) | ms | ✅ live |
| **laws** on traits, property-checked | algebraic wrongness (assoc/unit/idempotence…) | ms–s | ✅ ADR-0068 · #39 extends |
| derived generators + **`bang test`** | the declared-but-unchecked property gap | s | ✗ **the near gap** (#60) |
| differential oracles (kernel vs `--compiled`) | engine divergence | s | ✅ live |
| refinement/contract types | boundary predicates | s | ✗ post-v1, design-first |
| **proof export** (`#prove` a law → a Lean goal) | anything — full rigor, on demand | min–hrs | ✗ Q43, design |

Two properties make the ladder agent-shaped: every rung is **fail-loud** (a red build, a
non-zero exit, a located diagnostic — never a warning to scroll past), and every rung is
**declared in the program** (the `data` decl is the generator spec; the `law` is the property;
the row is the capability manifest) — the agent writes the gate as a side effect of writing
the code.

## HoTT — evaluated and set aside (2026-07-09)

Homotopy type theory's real payoffs (univalent transport across type equivalences; higher
inductive types/quotients) sit at the top of a prerequisite ladder bang deliberately avoids:
in-language types-as-propositions needs dependent types first, and elaborate-to-mono has now
won five times *because* the kernel stays simple. Two further blockers: Lean — bang's verifier
— is proof-irrelevant (not HoTT), so an in-language HoTT would fight the host foundationally;
and the agent economics point the opposite way (agents need fast decidable gates, not
search-heavy proof objects). The one idea worth remembering: univalence-flavored transport for
API migration — servable at bang's scale by ordinary isomorphism lemmas in the host. Revisit
only if bang ever grows dependent types (no current path intends it).

## The genuinely novel rung: proof export (Q43)

bang programs already elaborate into a Lean kernel that carries a verified semantics — no
mainstream language has that seam. So types-as-propositions does NOT require making bang a
proof assistant: a `#prove` pragma exports a `law`'s obligation as a Lean goal about the
ELABORATED kernel term, discharged in the host (by an agent or human), cached
content-addressed (ADR-0076's Merkle machinery — the proof stays valid exactly until the
term's hash changes; a stale proof is unrepresentable). The same `law` is **fuzzed by default,
provable on demand** — one construct, two rigor levels, an explicit seam. This is the
stratification principle (verified core / tested superset) surfaced into user programs:
"your paradigm is your row; your rigor is your rung."

## Build order (cheapest leverage first)

1. **#60 `bang test`** — runner over laws + generators derived from `data` decls (mechanical:
   the ADT is the generator spec), with shrinking (agents need minimal counterexamples). The
   Lean-level fuzz harness (#14, `Bang/Witness/Fuzz.lean`) is the template.
2. **#39** — law ergonomics (`=>` premise sugar, premise-aware sampling).
3. **Laws on effects** — a handler must satisfy its effect's declared laws; arrives with
   Stage 7 (#44) and IS the Q38 interface+laws convergence on schedule.
4. **Refinement types** — design-first, honestly weighed against "laws + boundary contracts"
   (which may cover most of it at a fraction of the cost).
5. **Q43 proof export** — design note → ADR after modules (ADR-0093) land; the
   content-addressing dependency is already pinned.
