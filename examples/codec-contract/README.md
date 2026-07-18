# Codec contract

One effect contract, two runtime realizations, and one shared conformance suite.

`Codec.bang` declares the operations and two round-trip laws. `Identity` and
`Shift7` are named handler realizations of that contract. The entry program selects
`Shift7` statically at the installation site; elaboration reuses bang's existing
custom-handler semantics, so this introduces no new kernel primitive.

```sh
lake exe bang run examples/codec-contract/main.bang
lake exe bang test examples/codec-contract/Codec.bang
lake exe bang query laws examples/codec-contract/main.bang
lake exe bang query dump examples/codec-contract/main.bang
```

The first command prints `35`. The second checks four instances: two laws across
two realizations. Both resolver-aware queries retain those imported instances as composable JSON
facts, with qualified `contract` and `realization` fields.

Effect-operation arguments are value positions today. Consequently, a nested
round trip is sequenced explicitly:

```bang
let encoded = codec.encode(x) in codec.decode(encoded)
```

This is the current CBPV boundary made visible, not special `Codec` syntax.
