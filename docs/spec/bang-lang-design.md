# bang-lang: paradigms, effects, runtimes

*Design notes — May 2026*

## Thesis

bang-lang is a small core on which paradigms, runtimes, and abstractions are built as ordinary library code.

- The **kernel** is thunks, effects, and STM.
- A function's **paradigm** is determined by which effects are in its effect row.
- A program's **runtime** is a value installed at the use site, not a property baked into the language.
- The choice of either is the programmer's, made explicit at the type level and at the call site.

Most languages bake paradigm and runtime into the syntax. bang-lang makes them parameters. The result: the same function can run pure, imperative, reactive, or concurrent depending on which effects are in scope and which handlers are installed.

---

## The kernel

The entire language is built from five primitives:

1. **Thunks.** Every value is a deferred computation. `let x = expensive()` does not run `expensive`; it captures it.
2. **Force.** The `!` operator evaluates a thunk to weak head normal form. `!x` is the only way to observe a value.
3. **Effect rows.** A function's type carries a row of effects it may perform. `fn f(): T with State, IO` declares that `f` returns `T` and may use `State` and `IO`.
4. **Handlers.** A handler is a value that implements an effect's operations. Installing a handler with `with` block makes the effect concrete at that point in the program.
5. **STM.** Software transactional memory is the one runtime primitive that can't be implemented as an ordinary handler, because its journal-and-retry mechanism needs compiler support. Every other concurrency mechanism is built on top of it.

Everything else — mutability, I/O, async, actors, signals, exceptions, logging — is library code expressed in terms of these five.

---

## Bindings

```
let x = 0          // immutable, the default
let mut x = 0      // mutable; only allowed inside functions
let sig x = 0      // signal: mutable + subscription tracking
let tvar x = 0     // transactional variable; usable only inside STM
```

**Top-level mutability is disallowed.** Global mutable state defeats testing, reasoning, and concurrency. If you genuinely need program-wide state, declare it as a resource accessed through an effect handler with explicit lifecycle. The escape hatch is verbose by design.

**Mutables and signals are different.** A mutable is a cell you can read and write. A signal is a cell you can read and write *whose readers are tracked*. Signal reads auto-subscribe inside a `Reactive` context; mutable reads don't. The cost of dependency tracking is paid only where it's asked for.

**TVars are different again.** A TVar can only be read or written inside an `atomically` block. The compiler enforces this. Outside STM, a TVar is opaque.

---

## Effect declarations

An effect is an interface of operations:

```
effect State[S] {
  get(): S
  put(value: S): Unit
}

effect Throws[E] {
  raise(err: E): Never
}

effect Send[Msg] {
  send(target: Process[Msg], msg: Msg): Unit
}

effect Reactive {
  subscribe(signal: Signal[Any]): Unit
  invalidate(signal: Signal[Any]): Unit
}
```

Effect declarations are **not** type declarations. An effect is an interface; the values implementing it are handlers. This is closer to a typeclass or a trait than to a struct.

A function declares which effects it may use:

```
fn parse(s: String): Int with Throws[ParseError]
fn read_config(): Config with IO, Throws[ParseError]
fn count_words(text: String): Int with State[Int]
```

The `with` separates the return type from the effect row. Effect rows are sets, not sequences — order doesn't matter, and rows compose via union.

For the common case of failure, `throws` is sugar:

```
fn parse(s: String): Int throws ParseError
// equivalent to:
fn parse(s: String): Int with Throws[ParseError]
```

---

## Handlers

A handler is a value that implements an effect:

```
fn state_handler[S](initial: S): Handler[State[S]] = handler {
  var current = initial
  get() => resume(current)
  put(v) => { current := v; resume(()) }
}
```

Installed via `with`:

```
fn count_words(text: String): Int = {
  with state_handler(0) {
    for word in split(text, " ") {
      put(get() + 1)
    }
    get()
  }
}
```

Inside the `with` block, calls to `get()` and `put()` dispatch to the installed handler. Outside, those operations aren't available.

**Handlers compose.** Multiple handlers can be installed simultaneously, and they can be swapped without changing the code they enclose. This is what makes runtimes-as-handlers work: the same program runs differently depending on which handlers are in scope.

---

## Actors

An actor is a structured form: state + protocol + receive loop.

```
actor Counter {
  state: Int = 0

  protocol {
    Increment: Unit
    Decrement: Unit
    Get(reply: Process[Int]): Unit
  }

  receive
    | Increment    => state := state + 1
    | Decrement    => state := state - 1
    | Get(reply)   => reply ! state
}
```

Using an actor requires effects:

```
fn use_counter(): Unit with Spawn, Send = {
  let c = spawn Counter
  c ! Increment
  c ! Increment
  let n = c ? Get      // ask-pattern, awaits reply
  print("count: \(n)")
}
```

**What makes actors different from objects:**

- **Identity, not reference.** You hold a process address, not a pointer. You can't dereference; you can only send.
- **Asynchronous.** `c ! msg` returns immediately; the actor processes when it gets to the message.
- **Isolated state.** Actors don't share memory. Sends copy the message (or move ownership).
- **Inherently concurrent.** Every actor is its own unit of scheduling. Concurrency isn't bolted on; it's the model.
- **Protocol-typed.** The protocol declares valid messages. Static checking can verify clients respect it.

The protocol declaration is what lifts actors above ad-hoc objects-with-mailboxes. It describes *valid conversations*, not just valid calls.

---

## Signals

Signals are mutable cells that track their readers:

```
let sig x = 0
let sig doubled = !x * 2     // auto-subscribes inside Reactive context

on doubled {
  print("doubled is now: \(!doubled)")
}

x := 5                        // doubled recomputes; on-block fires
```

The `!` operator behaves uniformly: it forces a thunk. Inside a `Reactive` context, forcing a signal also subscribes the current computation to that signal. Outside, it just reads the current value.

This is the bang-lang trick that makes signals feel native: there's no separate `signal.get()` API. You force them like any other thunk. The reactive effect is what makes the force *also* track the dependency.

---

## STM

STM is the privileged concurrency primitive. It can't be implemented as an ordinary effect because it needs compiler support for the transaction journal and retry mechanism.

### Core operations

```
effect STM {
  read_tvar[T](tvar: TVar[T]): T
  write_tvar[T](tvar: TVar[T], value: T): Unit
  retry(): Never
  or_else[T](first: () -> T with STM, second: () -> T with STM): T
}
```

Operators:
- `!tvar` reads a TVar (sugar for `read_tvar`)
- `tvar := v` writes a TVar (sugar for `write_tvar`)
- `retry()` aborts the current transaction and re-runs it when any TVar it read has changed
- `orElse` tries an alternative if the first transaction retries

A transaction is delimited by `atomically`:

```
fn transfer(from: TVar[Int], to: TVar[Int], amount: Int): Unit with STM = {
  let from_balance = !from
  when (from_balance < amount) { retry() }
  from := from_balance - amount
  to := !to + amount
}

// at the call site:
atomically { transfer(alice, bob, 100) }
```

### Worked example: bank transfers

```
// declare the accounts
let alice = tvar 1000
let bob = tvar 500
let charlie = tvar 0
let savings = tvar 5000

// the core transfer logic — pure STM
fn transfer(from: TVar[Int], to: TVar[Int], amount: Int): Unit with STM = {
  let from_bal = !from
  when (from_bal < amount) {
    retry()                                 // blocks until from changes
  }
  from := from_bal - amount
  to := !to + amount
}

// composed: try main account, fall back to savings
fn pay_from_either(
  main: TVar[Int],
  fallback: TVar[Int],
  recipient: TVar[Int],
  amount: Int
): Unit with STM = {
  transfer(main, recipient, amount)
    `orElse`
  transfer(fallback, recipient, amount)
}

// multi-step transaction: pay charlie and bob from alice atomically
fn pay_both(): Unit with STM = {
  transfer(alice, charlie, 100)
  transfer(alice, bob, 50)
  // either both happen or neither does
}

// running them
fn main(): Unit with IO, Spawn = {
  with thread_pool(cores=4) {

    // simple transfer
    atomically { transfer(alice, bob, 200) }

    // composed transfer with fallback
    atomically { pay_from_either(alice, savings, charlie, 2000) }

    // multi-step atomic transaction
    atomically { pay_both() }

    // concurrent transfers — STM guarantees serializability
    parallel {
      atomically { transfer(alice, bob, 50) }
      atomically { transfer(bob, charlie, 30) }
      atomically { transfer(charlie, alice, 10) }
    }
  }
}
```

### What STM guarantees

- **Atomicity.** Either every TVar write inside `atomically` becomes visible, or none does. No partial states.
- **Isolation.** Concurrent transactions don't see each other's intermediate states. Each transaction sees a consistent snapshot.
- **Composability.** Two transactions can be combined into one larger transaction simply by concatenating them inside a single `atomically`. This is the killer property: lock-based concurrency *cannot* compose this way, because acquiring two locks doesn't atomically combine two critical sections.
- **Retry, not deadlock.** If a transaction can't make progress (e.g. `from_bal < amount`), `retry()` parks it until a TVar it read changes. No locks, no deadlock, no priority inversion.
- **OrElse for alternatives.** `a orElse b` runs `a`; if `a` retries, runs `b`. Composable alternatives — try this, otherwise that.

### Why STM is in the kernel and not the library

The retry-on-change mechanism needs to know which TVars a transaction read so it can park the transaction and wake it when those specific TVars change. This requires runtime support that an ordinary effect handler can't provide — the runtime is journaling reads, tracking the read-set across the entire transaction, and reasoning about overlapping read/write sets for conflict detection. You could expose it through an effect interface (which we do — see the `STM` effect above), but the implementation must be a compiler-and-runtime primitive.

This is the one place where the "everything is a handler" principle has a ceiling. Worth being honest about.

---

## Runtimes as handlers

Concurrency, scheduling, time, and I/O are all effects. Their *implementations* are handlers. Which means choosing a runtime is a value-level decision:

```
fn server(): Unit with IO, Spawn, Send = { ... }

// production: thread pool, real I/O, real clock
with thread_pool(cores=8) {
  with real_io {
    with real_clock {
      server()
    }
  }
}

// testing: deterministic, instant
with single_threaded {
  with mock_io {
    with simulated_clock {
      server()
    }
  }
}

// sandboxed: I/O restricted to a whitelist
with thread_pool(cores=2) {
  with restricted_io(allowed_paths = ["/var/data"]) {
    untrusted_plugin()
  }
}
```

This unlocks:

- **Deterministic concurrent tests.** Install a deterministic scheduler and a simulated clock; concurrent code becomes a pure function from inputs to outputs. Property-based testing of concurrent systems becomes tractable.
- **Capability security.** A handler can decline to implement operations. Untrusted code can be given a restricted handler that only permits specific operations.
- **Profiling and observability without code modification.** Install a tracing handler; every effect operation gets logged. Install a metrics handler; every transaction is timed. The application code doesn't know it's being observed.
- **Gradual migration.** Move from green threads to OS threads by swapping a handler. The application logic is invariant.

---

## What's in the kernel vs the library

**Kernel (compiler and runtime support):**
- Thunks, force, lambda application
- Effect rows and handler dispatch
- Pattern matching, algebraic data types
- STM (journal, conflict detection, retry)

**Library (ordinary code over the kernel):**
- `State`, `IO`, `Throws` effects and their handlers
- `Reactive` effect and signal infrastructure
- `Spawn`, `Send`, `Receive` effects and actor runtime
- Async/await as a continuation-based handler
- Logging, metrics, tracing as effects
- All specific runtimes (thread pools, event loops, green threads, deterministic schedulers)
- All concurrency patterns built on STM (channels, semaphores, futures, queues)

The kernel is small enough to specify formally. The library is large but uniform: it's all the same shape (effect + handler), just with different operations and semantics.

---

## Open questions

- **Effect polymorphism.** What's the syntax for "this function works under any effect row that includes IO"? Probably row variables: `fn f(): T with IO, ...e`. Need to decide on inference vs. explicit annotation.
- **Recursive effects.** Can an effect's operations reference other effects? Probably yes, but the interaction with handler installation needs care.
- **Effect inference.** How much of the effect row can the compiler infer? Probably all of it for internal functions, with explicit annotation required at module boundaries.
- **STM and other effects.** Can a transaction perform I/O? Standard answer: no, because I/O is irreversible and STM may retry. But this is sometimes too restrictive. Investigate `unsafePerformIO`-style escape hatches and whether bang-lang wants them.
- **Mutables vs signals vs TVars.** Three mutable forms is one or two too many. Can `mut` and `sig` be unified? Probably not — the cost of subscription tracking is real. But the syntax should make the choice feel principled, not arbitrary.
- **Native backend.** Effect-TS transpile is the MVP. For native (LLVM, WASM), the Koka thesis on efficient algebraic effects via continuation passing is the reference.

---

## In one sentence

> *bang-lang's distinguishing claim is that paradigm and runtime are both values, not language features — and that a kernel of thunks, effects, and STM is enough to build everything else as ordinary library code.*
