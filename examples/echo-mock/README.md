# echo-mock

**ADR-0084 slice A**: an "IO is a paradigm-as-library" demonstrator. A `Net` effect
(`recv`/`send`) models a tiny echo-server session — a client sends 3 messages, the
server transforms each on `recv` and acknowledges on `send` — realized by a
**MOCK handler that is pure arithmetic over `Source.eval`, no syscall, no socket**.

```
effect Net { recv : Int -> Int, send : Int -> Int }

handle
  (let m1 = net.recv(7) in
   let a1 = net.send(m1) in
   let m2 = net.recv(13) in
   let a2 = net.send(m2) in
   let m3 = net.recv(21) in
   let a3 = net.send(m3) in
   a1 + a2 + a3)
with Net as net {
  recv(n) => n * 2 + 1,
  send(n) => n + 1000
}
```

```
lake exe bang run examples/echo-mock/main.bang    # 3085
```

## Why this is honestly a MOCK, not a server

ADR-0084 names the real gate: a genuine `{Net}` effect with `listen`/`accept`/real
sockets needs the FFI seam (Q37) + the compiled backend (◊5+) — right of the
mock-now/real-later line the ADR draws. This example stays strictly LEFT of that
line: `Net` is an ordinary user-declared `effect` (issue #44 Stage 7 / ADR-0095),
its ops are plain `Int -> Int` transforms, and its handler is pure arithmetic — no
byte ever crosses a process boundary. `recv`/`send` are the ADR's `read`/`write`
sketch, renamed: `get`/`put`/`raise`/`new`/`read`/`write` are RESERVED WORDS in v1
— the built-in ops they name (`state`/`throws`/`stm`'s own op-name table,
`Bang/Frontend/TypeCheck.lean`'s `capOpSig`) — so they can't even be PARSED as an
`effect`'s op name (confirmed live: `effect Net { read : Int -> Int }` fails at
the PARSER, `expected an identifier, got keyword 'read'`, before elaboration ever
runs); `recv`/`send`/`listen`/`accept` all parse and elaborate cleanly (confirmed
live) and carry the same request/response shape without the collision.

## The handler-swap story ("same body, different runtime")

The program's BODY — the sequence of `net.recv(...)`/`net.send(...)` calls — never
mentions how those operations are realized. Only the `with Net as net { … }` clause
block decides that. Today that block is:

```
recv(n) => n * 2 + 1,     -- mock "receive": tag + transform, no bytes read
send(n) => n + 1000       -- mock "send": tag + ack, no bytes written
```

A REAL handler for the exact same `effect Net { recv : Int -> Int, send : Int -> Int }`
interface — one that actually reads/writes a socket FD instead of computing an
arithmetic transform — would slot into that same `with Net as net { … }` position
with **zero change to the body above**. That is the whole ADR-0084/Q39 thesis in
miniature: the paradigm (here, "networked") is which effect is in the row; the
runtime (mock vs. real) is which handler is installed at the use site. Compare
`examples/stage-swap/` (the same shared-logic/swappable-installer pattern with two
DIFFERENT mock handlers already wired as separate `test`/`prod` installer
functions) and `examples/logger-counting/` + `examples/logger-silent/` (a handler
swap that changes what logging MEANS, not what the program says).

## v1 surface notes (pre-existing gaps, not this example's doing)

- **Reserved op names**: `get`/`put`/`raise`/`new`/`read`/`write` (the built-in
  effect ops) and `resume` (reserved for a future explicit-resume form, issue #93)
  cannot name a user effect's operation — confirmed live: `effect Net { read : Int
  -> Int }` fails to even PARSE (`expected an identifier, got keyword 'read'`);
  these names are reserved WORDS at the tokenizer, not just checked later at
  elaboration. This is why the op names here are `recv`/`send`, not the
  ADR-0084 draft's `read`/`write`.
- **RET-SHAPE restriction (ADR-0095 D4)**: a clause body must be a pure
  compute-then-resume value — no nested `perform`/`raise` before the resume value.
  Both clauses here are single arithmetic expressions, well inside that fragment.
  A "connection log" realized as MUTABLE handler state (a running counter a real
  server would keep) is out of reach in v1 for the same reason `logger-counting`'s
  README names: no mutable handler parameters yet (ADR-0092 D5 defers param-update)
  — counting/logging rides the return path, not a counter register.
- **Multi-clause handlers**: this example exercises TWO clauses (`recv`, `send`)
  in one `with` block — issue #86 (multi-clause handlers broken) is CLOSED
  (`46c888c8`); this file is itself a regression witness for that fix staying fixed.

See `docs/decisions/0084-networking-is-a-typed-effect-gated-on-user-defined-effects.md`
for the full mock-now/real-later design (options A/B/C/D, the prerequisite chain,
and why a bespoke kernel `net` constructor was rejected).
