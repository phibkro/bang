# carrier-inference-result

Issue #55 / ADR-0103 Amendment ②: a bound-free `let rec`'s free type
variable that appears ONLY in the declared RESULT type (never in any
argument) is now discoverable from the call site's own enclosing
annotation.

```
let rec mkNone : a -> Option b = fun ignored => None
```

`b` never occurs in `mkNone`'s argument (`a`). Before this fix, NO
annotation anywhere could close `b` — `discoverAtCall` only ever inspected
argument positions, so `docs/notes/carrier-inference-design.md`'s traced
root cause (`callSitesOf`'s `.annotS e t` arm discarding the annotation
before discovery ran) meant a call like `(($mkNone 3) : Option Int)` still
failed "a use leaves a type variable unresolved," even with the result
annotated, because that annotation was never consulted.

**The fix**: `callSitesOf`/`redirectCalls` gained a `discoverAtCallResult`
door mirroring the existing argument-position `discoverAtCall` — reusing
the SAME fully-general `matchTyVars` unifier, no new inference power. Two
independent instantiations of the same result-only tyvar in one program
produce two DISTINCT monomorphic residues, exactly the distinct-
instantiation discipline ADR-0103 already established for arguments.

**The fail-loud extension this door needed** (and the argument-only door
never did): an argument annotation and a result annotation disagreeing on
the same type variable is a genuinely contradictory program — refused
loud (`B017`) naming both conflicting types, never silently picked.

```
lake exe bang run examples/carrier-inference-result/main.bang
# mkNone instantiated at Option Int (residue 1) then Option Char (residue 2)
# in the SAME program -> 11 + 22*100 -> 2211
```
