# lattice-store

The first concrete R3 evidence is a generic, axiom-clean Lean lattice core plus the BANG consumer
that found the next surface wall. It is deliberately **not** presented as a completed end-to-end
CALM tracer.

`Bang/Distribution/LatticeStore.lean` defines a store whose only representable update is join. It
proves the fragment's actual laws: an update is inflationary, two updates commute, duplicate
delivery is idempotent, and two stores agree after one symmetric anti-entropy exchange. The last law
assumes that exchange; it is not a network-liveness theorem or a general CALM theorem.

## The consumer-pulled wall

`computed-update-wall.bang` is the smallest honest `Int/max` handler for the intended surface:

```bang
update joinPut(value) =>
  (if param < value then value else param,
   if param < value then value else param)
```

Both pair components are pure computations. ADR-0114 currently requires the two components of an
updating clause's outer pair to be syntactic values, so checking this source must fail with:

```text
update clause 'joinPut' must return a value pair `(resumeValue, nextParam)`
```

This is a shared frontend boundary, not lattice-store-specific syntax. The allocator transition
found the same restriction. One follow-on increment should own **pure computed update components**
once, with both the allocator transition and this max-join handler in its acceptance matrix.
Effectful clauses, finalizers, the full D5 proof port, grade-polymorphism, and consumer-specific
operations are outside that increment.

The example does not replace generic join with one constant operation per lattice element, compute
the join at every caller, or otherwise fake a runnable monotone store.

## The independently excluded operation

`cas-excluded.bang` calls `store.cas((expected, replacement))`. Its handler uses a direct value pair,
which ADR-0114 accepts, so the retained diagnostic isolates the intended API boundary:

```text
unknown operation 'cas' for effect 'LatticeStore_Store'
```

`just test-lattice-store` requires both refusals. This branch adds no coordinating CAS, `coord` row
label, kernel primitive, arbitrary merge certification, or claim that BANG programs are generally
coordination-free.
