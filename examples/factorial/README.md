# factorial — the bignum milestone (issue #132, bignum lane B3)

`fact 25 = 15511210043330985984000000`, far past `2^63` (`9223372036854775808`). Recursive
multiplication: each `n * fact(n-1)` starts on the i64 fast path and, once the product exceeds i64,
`$mulVal` promotes to a `$bigval` and does a schoolbook limb multiply. The first bang program
computing an arbitrary-precision result outside Lean — before B3 the compiled path silently WRAPPED
past `2^63`. `expected.txt` is `bang run`'s stdout.
