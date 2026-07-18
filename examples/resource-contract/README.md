# Resource contract

This example is the first vertical slice of BANG as a language of semantic descriptions.
`Permit` declares an operation and a law; `Identity` and `Negate` are alternative realizations.
The entry program then declares two local resource obligations:

- `use [1] permit` requires the installed capability to be consumed exactly once.
- `use [0] ghost` proves the value is unused. The assertion erases before lowering, and the Wasm
  backend evaluates the binding expression but omits its dead environment cell.

```sh
lake exe bang check examples/resource-contract/main.bang
lake exe bang run examples/resource-contract/main.bang
lake exe bang test examples/resource-contract/Permit.bang
lake exe bang query contract examples/resource-contract/main.bang
lake exe bang emit examples/resource-contract/main.bang -o /tmp/resource-contract.wat
```

The program prints `7`; both handler realizations satisfy `preserves_zero`. The contract query
returns contracts, realizations, quantities, laws, and compiler evidence in one JSON document.
The refusal fixtures in `scratch/resource-contract/` pin duplicate and forgotten permit errors.
