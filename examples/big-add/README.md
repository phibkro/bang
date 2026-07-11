# big-add — bignum addition, i64-overflow from in-range operands (issue #132, bignum lane B2)

`(2^63-1) + (2^63-1) = 18446744073709551614` overflows i64 from two IN-RANGE operands — the case a
plain `i64.add` would wrap. `$addVal` takes the i64 fast path, detects signed overflow via
`(a^s)&(b^s) < 0`, and promotes to a `$bigval` limb sum. `expected.txt` is `bang run`'s stdout.
