# hostio-echo

**ADR-0104, the host-IO wedge.** A program that imports the bundled `std/Io.bang`
module and performs `Console` operations (`print`, `readLine`) — the first bang
program whose effects are *host* IO rather than pure library effects.

```
import Io
let main =
  handle
    (let prompt = SCons(Char(63), SNil) in    -- "?"
     let u1 = con.print(prompt) in
     let line = con.readLine(()) in
     let u2 = con.print(line) in
     $reverse line)
  with Io_Console as con {
    print(s)    => (),                          -- SIM: swallow the line
    readLine(u) => SCons(Char(104), SCons(Char(105), SNil))   -- SIM: a FIXED line, "hi"
  }
```

```
lake exe bang run examples/hostio-echo/main.bang    # ih   (reverse of the fixed "hi")
```

## The sim-corpus / real-battery split (why this runs under SIM here)

The example harness (`tools/check-examples.sh` + `tools/check-examples-env.sh`) runs
every `examples/*/main.bang` under the **default runtime**, which for host IO is the
**sim environment** (`--env=sim`): pure, deterministic, no real syscall, so its output
is a stable `expected.txt` the harness can diff byte-for-byte on BOTH engines (the
oracle and `--engine=env`). That is exactly what this example does — the `with
Io_Console as con { … }` block installs SIM clauses: `print` swallows the line,
`readLine` returns a FIXED constant. The program is fully deterministic, so `ih` is a
faithful corpus oracle.

The **real** path — `--env=real`, actual `IO.println`/`readLine`, then `--record` a
trace and `--replay` it back under the sim on the pure oracle — is deliberately NOT a
corpus entry: it needs a granted host environment and live stdin, which the sim-only
harness cannot supply. It is exercised instead by **`tools/test-hostio.sh`** (enrolled
in `run-batteries.sh`): a scripted Console program recorded under `--env=real` then
`--replay`'d reproduces byte-identical output — the invariant-#1 trace-replay gate
(ADR-0104 §3). Splitting it this way keeps the corpus purely deterministic while the
real host boundary still gets watched end-to-end where it can be.

## Same body, different runtime

The body — the sequence of `con.print(...)` / `con.readLine(...)` calls — never says
HOW those operations are realized. Only the handler block decides that:

- the **SIM** clauses above (swallow + fixed line) — the default, verified-core runtime;
- a **REAL** Console handler (the host driver in `Main.lean`, `--env=real`) that does the
  actual terminal IO and records each `(label, op, payload, result)` row.

Swapping sim → real is a runtime choice (`--env`), not a body change — the ADR-0084/0104
"paradigm is the row, runtime is the installed handler" thesis, now on the *host* axis.
`Console` is a plain `pub effect` in `std/Io.bang`; nothing kernel-new (invariants #4/#5).

## Least-authority

The program must `import Io` to name `Console` at all — so `main`'s effect row is its
**capability manifest** (ADR-0093 D5): a reader sees `{Console}` and knows exactly what
host surface this program can touch. Host IO is never ambient (it is NOT in the always-open
prelude); a dependency cannot quietly acquire it without the acquisition showing up in its
signature. See `docs/decisions/0104-host-io-environment.md` and
`docs/notes/host-io-design.md` for the full design.
