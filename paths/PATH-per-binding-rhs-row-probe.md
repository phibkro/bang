# PATH-per-binding-rhs-row-probe — stop when checker rows have no sound source identity

> Locate the checker's real RHS-row seam, falsify name/position attribution after elaboration, and
> price explicit binding provenance without laundering cumulative rows into declaration-local facts.

## Seam

- **From checkpoint**: `PATH-top-level-initializer-census` left 17 conservative computation-form
  occurrences and named checker-cooperative RHS rows as the preferred refinement.
- **To checkpoint**: the checker capture point is located, but its attribution contract is refuted by
  accepted source programs and generic specialization. No row schema is exposed.
- **Contract preserved**: inference, elaboration, query JSON, execution, and the existing meaning of
  `DeclFact.row` remain unchanged.

## Actor journey / observable outcome

- **Actor / need**: a build-tool author wants the effect row of one source declaration's initializer,
  computed by the authoritative final inference rather than a second elaboration.
- **Positive seam**: final `synthSC` has the binding name and RHS row `φ₁` together in its `.lett` arm.
  A raw `Row` could be accumulated and resolved against the final substitution after inference.
- **Failed identity seam**: by that point the checker sees an elaborated `Surf` tree, not source
  declarations. User, alias, recursive-knot, monomorphized, prelude, and ANF lets share one constructor
  and carry no origin marker.
- **Terminal observation**: stop before schema design. A correct implementation first needs explicit
  binding-occurrence provenance through elaboration, or a separately justified checker/elaborator
  refactor. Name filtering and positional alignment are both unsound.

## Feeds the constraint

- **Binding constraint now**: the future link/initialization contract needs declaration-local evidence,
  but `DeclFact.row` is chain-cumulative and the final checker has no source-occurrence identity.
- **How this path feeds it**: preserve the exact representation wall, forbid guessed attribution, and
  close the currently bounded decision input through the manual residual audit in
  `PATH-top-level-initializer-census`.

## Kill shots

| probe | source declarations | elaborated outer let spine | consequence |
|---|---|---|---|
| duplicate plain lets | `let x`; `let x`; `let main=x` | `x, x` | a name does not identify an occurrence |
| recursive/plain collision | `let rec x`; `let x`; `let main=x` | `#rec, x, x` | user and recursive-desugaring bindings collide |
| internal spelling | `let #rec=1`; `let main=#rec` | `#rec` | the internal prefix is user-spellable |
| bare alias | `let x=1`; `let alias=x`; computed `y`; `main=y` | `x, y` | source declarations can disappear before checking |
| generic specialization | source has only `let rec length` | `#rec, #mono0_Prelude_take, #rec, #mono0_Prelude_drop, #rec, #mono0_length, nums, firstThree, lastTwo, #anf6, #anf7` | specialization and ANF insert source-unowned outer lets |

The first four probes were minimized against the parser and `elabProg`; the fifth is the retained
`examples/list-basics` generic witness. Together they satisfy the stop bar more strongly than a single
synthetic collision: both candidate attribution strategies fail on ordinary accepted programs.

## Prospective systemic review

| concern | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|
| publish a synthetic let's row as a source fact | realized / critical / high | **stop; no schema** | explicit occurrence provenance survives elaboration |
| publish an under-zonked open row | high / high / medium | require raw capture + final substitution | attribution door reopens |
| re-run each RHS and drift from final inference | high / high / high | reject second elaboration as the fact authority | checker exposes a supported per-binding API |
| refactor the checker for one speculative consumer | medium / high / high | price provenance at 1.5 consumers, do not build | a second concrete consumer arrives |
| lose the initialization-contract decision entirely | low / high / low | manually audit the enumerable 17-site residue | a site cannot be classified by source reading |

## Plan

1. [x] Locate the final-inference capture point and establish zonk-late requirements.
2. [x] Probe duplicate, internal-name, alias, recursive, generic, and ANF attribution.
3. [x] Stop schema work when both name and position identities fail.
4. [x] Record explicit provenance as a priced Q34 door and hand-audit the bounded residue.

## Status

- [x] Started 2026-07-18
- [x] Completed-as-refuted 2026-07-18
- [ ] Product blocker: explicit binding-occurrence provenance through elaboration has only one current
  hard consumer (RHS rows) plus one plausible future consumer (file-aware diagnostics).
- Reopen only when another concrete consumer raises that demand, or a future elaboration representation
  supplies provenance as part of independently justified work.
- No executable or schema changes landed from this probe.

## Owner

- Agent / human: Codex, with persistent Fable 5 advisor in Herdr `lang-bang`
