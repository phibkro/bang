# handle-custom-nested

Two **simultaneously active** handlers of the same effect (`Net`), nested. Pins
the core dispatch principle (glossary in `CLAUDE.md`): **typing is by label,
dispatch is by identity** (ADR-0052, ADR-0055). `outer.fetch(2)` must dispatch
to the *outer* handler by capability identity even though the *inner* handler
of the same effect is nearer on the stack — a nearest-label dispatcher would
route it to the inner handler instead and print `30` rather than `210`.

No existing example in this corpus nests two active handlers of one effect
(`stage-swap` selects handlers sequentially, never nested), so this closes
that gap in the run-oracle gate (`tools/check-examples.sh`).
