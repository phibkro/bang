# The description/value distinction

*bang-lang design notes — May 2026*

## The central claim

The most important distinction in bang-lang is not "everything is a thunk." It's the difference between a *description of a computation* and the *value that computation produces*, made syntactically visible:

- `name` — a description. Unevaluated. A recipe. The address of the work, not the work's result.
- `(name)` — force it. Run the recipe now, produce a value.
- `(f a b)` — force the application of `f` to `a` and `b`.

"Everything is a thunk" is the mechanism. The description/value distinction is the *point*. It explains why laziness is powerful here rather than merely unusual: a bare name is a first-class, inspectable, serializable representation of work-to-be-done, and forcing is the explicit act of turning that representation into a result.

Three features that other languages treat as separate, hard-won capabilities fall out of this one distinction applied consistently at different scales.

## Scale 1: reactivity

On a mutable binding, the right-hand side of `=` can be bare or forced, and the choice is the difference between a live link and a dead snapshot.

```
mut x :: Int
x: 2
mut y :: Int
y: 3

x = y          # live unification — x tracks y's identity, follows its changes
y = (y + 1)    # force y+1 to 4, drive y to 4 — x reacts, x is now 4

x = (y)        # snapshot — force y now, freeze x at that value, sever the link
y = (y + 1)    # y becomes 5 — x does NOT react, x stays 4
```

Bare `y` on the right of `=` subscribes. `(y)` samples. The parens are the untrack operation that other reactive systems implement as a primitive (`untrack` in SolidJS, `toRaw` in Vue, `untracked` in MobX). Here it's not a primitive. It's the same forcing that parens do everywhere, and severing the reactive link is just what forcing happens to mean in this position.

Note: `y = (y + 1)` must force the right side. Bare `y = y + 1` would attempt to bind `y` to a live expression referencing itself — a self-referential reactive cell, which is either a recursive signal or an infinite loop. Increment wants a number, so increment forces.

## Scale 2: the `:` versus `=` boundary

`:` introduces a binding. `=` drives an existing mutable cell to a new state.

- `x: 2` — introduce x. Silent. Nothing was watching; the binding came into being.
- `x = 3` — update x. Reactive event. Subscribers are notified.
- `x: 4` on an already-introduced x — error. Use `=` to update.

Reactivity fires on `=`, never on `:`. Introduction is silent; state-transition is observable. This collapses four concepts from typical reactive languages (declare, assign, create-signal, update-signal) into two operators whose distinction *is* the reactive boundary. The `sig` keyword is unnecessary: a value is reactive if it's `mut` and updated with `=`. The programmer chooses reactivity by choosing the operator.

This extends uniformly to structs and maps, because a struct literal is just a scope of bindings:

```
point: { mut x: 3, mut y: 4 }   # fields introduced with `:`, individually mut
(point.x = 5)                    # reactive update on point.x specifically
```

Per-field reactivity, no wrapper type. The `mut` marker is the wrapper, syntactically. Reactivity is fine-grained by default: `point.x = 5` notifies subscribers of `point.x`, not the whole struct. Watching the whole struct means subscribing to a derived value that reads all fields.

## Scale 3: computation as data

A bare name is a serializable description of work. This is the largest payoff.

If `name` is the unevaluated recipe and `(name)` is the result, then a thunk can be passed around, stored, hashed, sent over a network, or written to disk *as a description*, with forcing deferred to the destination. This is the substrate for three things bang-lang wants:

**Content-addressed incremental evaluation.** Hash the description, cache by hash, recompute only when the description changes. This is Unison's model: code is content-addressed by the hash of its unevaluated syntax tree, which is what gives Unison no-build and conflict-free dependencies. In bang-lang this is the default state of every binding rather than a special feature. Every binding is a hashable description until forced. This is the foundation for the compiler-equals-build-system idea: the build graph is the thunk graph, and content addresses are the cache keys.

**Distributed computation.** Serialize `compute-heavy` (the thunk, small) rather than `(compute-heavy)` (the result, potentially huge), ship it to where the data lives, force it there. Move code to data instead of data to code. This is the MapReduce/Spark premise, and here it's just "send the bare thunk, force remotely." The reference/dereference distinction is the local/remote distinction made syntactic, and it maps directly onto the communication axis of the resource trinity: sending `name` spends communication on a description; sending `(name)` spends it on a value. The programmer picks which resource to spend by picking parens or not.

**Durable and resumable execution.** Effect handlers capture the rest of a computation as a continuation. If continuations are thunks and thunks serialize, a paused computation can be persisted and resumed later, on another machine, after a restart. Durable execution engines (Temporal, Golem, Azure Durable Functions) build elaborate machinery to serialize computation state because host languages don't treat computations as first-class serializable things. Bang-lang gets it from the core: a suspended effect is a bare thunk, and bare thunks serialize.

### The closure-serialization problem

Serializing a thunk means serializing its free variables — everything the description references. If `expensive` references `config` and `data`, shipping `expensive` means shipping those too. This is the hard part, and it's a real design fork:

- *Require serializable captures*, checked by the type/effect system. A thunk is serializable only if its free variables are. This makes serializability a tracked property, possibly an effect or a type-class constraint.
- *Content-address everything*, Unison-style, so free variables are just more hashes to ship and resolve at the destination.

The syntactic foundation (bare-name-is-a-shippable-description) supports either answer. The choice has consequences for the runtime and the distribution story, and it interacts with the scope question below.

## Implicit closures may be a mistake

Right now a bare thunk implicitly closes over its lexical environment. This is convenient and it's also the source of the serialization problem, hidden coupling, and surprising memory retention (a thunk keeps its whole captured environment alive until forced or dropped).

There are now *two* channels for passing things into a computation:

1. Direct arguments — explicit, visible in the signature.
2. Effects — explicit, visible in the effect row.

If both of those channels are explicit and tracked, the question arises: why allow a *third*, implicit channel (lexical capture) that is neither visible in the signature nor tracked in the effect row? Implicit closures smuggle dependencies in through the back door. Everything bang-lang's type and effect system is trying to make visible, closures make invisible again.

A radical option: **disallow implicit capture. Every dependency must arrive as an argument or an effect.** A thunk references only its parameters and its declared effects, nothing from the enclosing scope. This is more verbose but it makes every thunk trivially serializable (no hidden captures), makes dependencies fully visible, and removes a class of memory-retention surprises. It's the same discipline that makes pure functions easy to reason about, extended to capture.

This leads directly to the next question.

## What if every scope is its own scope, not nested in its parent?

The proposal: lexical scopes do not see their enclosing scope's bindings. Each scope is closed. A function body sees its parameters and its effects, not the variables of the surrounding function or module.

### What this breaks

A great deal of ordinary convenience:

- Helper closures that capture a loop variable or an outer accumulator stop working — you must pass everything explicitly.
- Currying and partial application become awkward, because a returned function can't close over the already-applied arguments. You'd need to thread them as explicit state or as an effect.
- Module-level constants aren't visible inside functions unless imported or passed. Every function that uses a config value takes it as an argument or reads it through an effect.
- Common functional idioms (a `map` whose function references an outer variable) require restructuring so the outer variable comes in as an argument.

### What it buys

- Every thunk is trivially serializable. No hidden captures means the closure-serialization problem disappears. Distribution and durable execution become straightforward.
- Dependencies are fully explicit. A function's complete input surface is its parameters plus its effect row. Nothing arrives invisibly. This is maximal honesty about data flow.
- Memory behavior is predictable. A thunk retains only what it was explicitly given, not an entire captured environment.
- It composes with the resource trinity framing: every value crossing a scope boundary is a deliberate, visible act of communication, never an implicit reference into a parent frame.

### The likely resolution

Full scope isolation is probably too austere for daily use — the loss of capture makes ordinary code painful. But the *instinct* is right, and there's a middle path borrowed from a few places:

- **Explicit capture lists**, the way C++ lambdas (`[x, &y]`), Swift (`[weak self]`), and Rust (`move`) make capture a visible, deliberate act rather than an implicit one. A thunk declares what it captures. Capture is allowed but never silent.
- **Capture as a checked property.** A thunk that captures non-serializable things is itself non-serializable, and the type/effect system tracks this. You can capture freely, but the consequences for serializability are visible in the type.
- **Module constants exempt.** Top-level immutable bindings (which are content-addressable and shippable as hashes) can be referenced freely, because they don't create the retention or serialization problems that capturing mutable local state does.

So: not "every scope is fully isolated," but "capture is explicit and tracked, and the default leans toward passing things as arguments or effects rather than capturing them." The austere version is the right thing to *measure against* even if the shipped version is more permissive. The principle: a dependency should be invisible only if it is also free (immutable, content-addressed, cheap to ship).

## Reversibility: programs as groupoids

A speculative direction. If every operation has a declared inverse, then computation becomes reversible, and the algebraic structure of programs shifts from monoid to groupoid.

### The algebra

A monoid is a set with an associative binary operation and an identity. Function composition forms a monoid: composing functions is associative, and the identity function is the unit. Ordinary programs are monoidal — you compose operations forward, and there is no general way back.

A groupoid is a category in which every morphism is invertible. If every operation `f` has an inverse `f⁻¹` such that `f⁻¹ ∘ f = id`, then the program's operations form a groupoid: you can always run backward as well as forward.

### What reversibility would require

- Every primitive operation declares an inverse. Addition's inverse is subtraction; a struct field set's inverse is restoring the prior value; an effect's inverse is a compensating effect.
- No information is destroyed without recording how to recover it. Reversible computing (Bennett, Toffoli, Landauer) makes this precise: the irreversible operation is *erasure*, and erasure has a thermodynamic cost (`kT ln 2` per bit). A reversible program never erases; it threads the information needed to undo each step.
- Effects need compensations. This is already a known pattern in distributed systems: the saga pattern compensates committed steps with explicit inverse operations when a later step fails. Reversible effects generalize sagas to the whole language.

### What it would buy

- **Time-travel debugging for free.** If every step is invertible, stepping backward through execution is just running the inverses. No replay-from-start, no snapshotting.
- **Undo as a language primitive.** Application-level undo (the thing every editor reimplements) becomes a consequence of reversibility rather than a feature to build.
- **Speculative execution with clean rollback.** This is exactly what STM does — optimistic execution, roll back on conflict. Reversibility makes rollback a general capability, not an STM-specific one. STM's journal is the reversibility information for transactional memory; generalize it and every effect carries its compensation.
- **Bidirectional transformations.** Lenses, parsers-that-are-also-printers, and serializers-that-are-also-deserializers all want a forward and a backward direction that provably agree. A groupoid structure makes "the backward direction" a first-class thing the language tracks.

### How it interacts with the rest of the design

Reversibility and the description/value distinction reinforce each other. A bare thunk is a description; if descriptions carry their inverses, then a serialized computation can be shipped, run forward at the destination, and *unwound* if the result needs to be rejected. Durable execution plus reversibility is exactly the saga pattern, but derived from the algebra rather than hand-built.

Reversibility also bears on the scope question. A reversible operation cannot silently destroy a captured variable's old value — it must record it to undo. Scope isolation and reversibility both push toward the same discipline: make information flow explicit, never destroy without recording, never capture without declaring.

### The honest caveat

Full reversibility is expensive. Threading undo information through every operation costs storage (the trinity again — you spend storage to buy the ability to run backward). Most programs don't need to run backward most of the time. The realistic version is *opt-in reversibility*: a `reversible` effect (or region) within which operations carry their inverses, and outside which they don't. STM is then a special case — a built-in reversible region with a particular conflict-detection policy. The groupoid structure exists where you ask for it and collapses to the cheaper monoid where you don't.

This mirrors the whole bang-lang philosophy: the powerful, expensive capability is available as an effect you opt into, the cheap default is what you get when you don't, and the type system tells you which one you're in.

## Open questions raised here

- Is serializability a tracked effect, a type-class constraint, or a property derived from content-addressing? The choice shapes the distribution story.
- Capture lists: what syntax, and how does the effect system represent "this thunk captures these things"?
- Are module-level immutable bindings genuinely free to reference, or do they also need to be explicit for full honesty?
- Reversibility as effect versus reversibility as region: which composes better with handlers?
- Does the inverse of an effect operation live in the effect declaration, or in the handler? (Probably the handler, since different handlers might compensate differently — but then the inverse isn't a property of the operation, it's a property of the interpretation, which is interesting.)
- If `:` introduces once and `=` updates, what is the semantics of re-entering a scope (a loop body, a recursive call)? Does each entry re-introduce, and if so, is that an event?
