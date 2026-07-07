---
type: design-question
title: "Handler-application syntax: prefix binder vs postfix eliminator (the effect eliminator wants eliminator syntax)"
description: "handler = the effect ELIMINATOR; ambient application → postfix eliminator, named caps → prefix binder"
status: open
area: surface
ties: ["ADR-0070", "ADR-0071", "ADR-0072"]
see-also: ["#44"]
---
**Question**: should installing a handler be spelled as a PREFIX binder (`state 5 as h in body`, today)
or a POSTFIX eliminator chained on the body (`body ⟨…⟩ state 5`, Effect-TS/ZIO-style)?

**Why it matters** — *"syntax should serve and communicate semantics, not the other way around"*
(Pratt, via Cheng-Parreaux ECOOP'26 §Introduction, the paper behind ADR-0071). The current syntax
**mis-signals** the semantics. A handler is not a binder that happens to scope a body — it is the
**ELIMINATOR for effects**, the dual of the introduction/sequencing constructs (grounded in the
checker):
```
perform / h.get / raise    ADD ℓ to the row       INTRODUCE an effect  (φ ∪ {ℓ})
let x = e in body          UNION the rows          SEQUENCE             (φ₁ ⊔ φ₂)   ← NOT an eliminator
handler install            ERASE ℓ from the row    ELIMINATE an effect  (φ.erase ℓ) + delimit conts
```
So **handler : effects :: match : data** — both are eliminators, both correctly separate from `let`
(sequencing). This answers a related question ("why is handler-install a separate construct from
`let`?" — because it eliminates + delimits; `let` only sequences). But the PREFIX-binder spelling
(`state 5 as h in body`) dresses an eliminator as a binder, which is exactly why it keeps reading
awkwardly (the `with … as` wart ADR-0072 already trimmed once). POSTFIX reads as elimination —
`body.handle(state 5)` parallels `data.match(…)`; the syntax finally matches the operation.

**Detail — the regime split (load-bearing):**
- **AMBIENT effects** (row = deps, bubble up, ops resolve to the nearest lexical handler): postfix is
  a *pure syntactic reorder* — `state 5 in body` and `body ⟨install⟩ state 5` scope identically, only
  the reading order differs. It matches the mainstream Effect-TS/ZIO mental model (R in the type,
  handlers `provide`d postfix, handle-location flexible) — squarely on-moat ("safe to generate into").
- **NAMED capabilities** (explicit `Cap ℓ` value, ADR-0070/0072): CANNOT go postfix — `state 5 as h in
  body` binds `h` INSIDE `body`, but postfix writes `body` first, so `h` isn't in scope. Lexical
  capability binding structurally requires the handler to ENCLOSE the body (prefix). This is why
  Effect-TS *can* be postfix (ambient ops, no binder) and Koka/Effekt named handlers can't.
  ⟹ the clean split: **ambient application → postfix eliminator; named caps → prefix binder.** Two
  syntaxes, but principled — they mark two genuinely different regimes.

**⚠ The line to hold:** postfix `provide`-chaining as SUGAR OVER THE LEXICAL kernel (handler still
encloses a directly-written body) is cheap + sound. The FULL ZIO/Effect-TS *environment/reader* model
— pass an effect VALUE around (a thunk) and `provide` it later at the top — drifts toward
reader-passing, a bigger and possibly-unsound-under-lexical-dispatch (ADR-0052) fork. Keep
"postfix-sugar-over-lexical" and "full environment-passing" SEPARATE.

**Options**: (1) **status quo** — all prefix (`state 5 [as h] in body`, ADR-0072). (2) **ambient
postfix + named prefix** (recommended direction) — the eliminator framing made visible; matches the
mainstream model for the common case; named stays lexical-prefix. (3) full-environment (ZIO `R`+provide)
— rejected-for-now (the ⚠ line).

**Recommended**: (2) as the *direction*, but design-first (an ADR, not a snap change — unlike ADR-0072
which was cosmetic). Open sub-decisions: the exact postfix SPELLING (bang's `.` is already cap-perform,
`h.get`, so handler-application needs a DISTINCT token — not `.handle`), whether ambient+named
two-syntaxes is acceptable, and the thunk/environment boundary.

**Blocked on**: nothing hard — a design pass + ADR. Interacts with #44 (user-defined effects: a
user handler is also an eliminator, so its syntax should follow whatever this decides) and the
`handle`/`state`/`atomically` keyword-regularization deferred by ADR-0072.

**Revisit signal**: taking up #44 (user-defined effects & handlers — settle handler *application*
syntax as part of it); or agent/user ergonomics friction from the prefix-binder-dressed eliminator;
or when the effect surface-model is deliberately chosen (Koka-lexical vs Effect-TS-environment lens).
