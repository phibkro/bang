# traitop-namecall

Issue #78 / ADR-0106: trait ops are now callable by NAME, not just through
an operator overload (`==`/`<`). Before this fix, `showIt(x)` — a bare
name-call on a trait op — was `unbound variable`, no matter how many impls
existed; only `env.insts` consulted at the `.binopS` arm could dispatch.

```
trait ShowT { fn showIt(x) -> Int }
impl ShowT for Box { fn showIt(x) = match x { B(n) -> n } }
showIt(B(42))    -- 42, dispatches through the impl by NAME
```

**Lexical shadowing** (ADR-0005/0006's "no implicit capture", extended to
this new name-resolution site): a user's own binding of the same name wins
UNCONDITIONALLY — the trait op is never even consulted once `Γ` already
binds the name.

**Self-recursion** through the same mechanism, on a recursive carrier,
needed the `#112` knot-dispatch door (previously arity-2-only, since
`.binopS` never reached any other arity) generalized to any arity ≥1 —
`total(t)` recursing on `MyList`'s own tail now resolves the same way a
hand-written `eq`/`lt` op's self-call always has.

`deriving (Show)` is unlocked for its ONE fully-working shape: an
all-nullary carrier, where the generated impl never needs a prelude
conversion call. A carrier with any non-nullary ctor hits a SEPARATE,
pre-existing `#112`-vintage knot-scoping wall (documented in ADR-0106 §5,
found but not fixed this session) — out of scope here.

```
lake exe bang run examples/traitop-namecall/main.bang
# a=42 (unshadowed dispatch) + b=1005 (shadowed, user fn) +
# c=6*10000 (self-recursive dispatch) + d=9*1000000 (derived Show, nullary)
# -> 9061047
```
