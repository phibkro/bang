# big-literal — bignum literal round-trip (issue #132, bignum lane B1)

`99999999999999999999` is past `2^63` (`9223372036854775808`). bang's kernel `Int` is unbounded ℤ.
Before B1 the WasmGC emitter emitted `(i64.const 99999999999999999999)` — invalid wat (out of i64
range), so a big value could not round-trip at all. Now the emitter emits a `$bigval` (base-10⁹
sign-magnitude limb array) and the WASI printer (`$emitBig`) renders it byte-identical to `bang run`.

No arithmetic yet — that is bignum lane B2/B3. This example gates the REPRESENTATION + decimal
READBACK. `expected.txt` is `bang run`'s stdout.
