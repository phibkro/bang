# pledged-plugin

An effect-row boundary around untrusted plugin logic. The plugin receives an `Audit`
capability and voluntarily states its complete authority ceiling:

```bang
pledge {Policy_Audit} in audit.record(41)
```

`Policy` also declares a `Secret` effect to make the denied authority concrete. Adding a
`secret.reveal(...)` operation inside the pledged region is a type error: the inferred
`{Policy_Audit, Policy_Secret}` row is not a subset of the declared `{Policy_Audit}` ceiling.
The accepted program installs the reusable `Policy_Count` handler and prints `1`.

`pledge` is a compile-time row assertion, not a runtime filter. It restricts which effect
labels may occur and then erases before lowering; handlers still decide what each admitted
operation means. Value-level restrictions such as filesystem paths remain handler policy.

```sh
lake exe bang check examples/pledged-plugin/main.bang
lake exe bang run examples/pledged-plugin/main.bang  # 1
```
