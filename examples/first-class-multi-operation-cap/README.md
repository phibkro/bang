# First-class multi-operation capability

`Register` crosses a function boundary as `Cap Register`, so concrete Wasm must dispatch from the
runtime capability rather than a lexical handler slot. The function invokes two distinct operations:
plain `inspect` reads the parameter, updating `advance` changes it from 2 to 5, and a final `inspect`
must observe 5. The encoded result is therefore `2 * 100 + 5 * 10 + 5 = 255`.

This is deliberately stronger than a two-operation smoke test. Reversing or guessing clause position,
using one handler-wide update bit, failing to persist the updated parameter, or dispatching by an
inexact operation identity changes the result or traps on concrete Wasm.
