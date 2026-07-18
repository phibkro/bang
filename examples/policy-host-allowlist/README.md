# policy-host-allowlist

One unchanged plugin, one `Net` effect row, and two runtime-configured host policies.

The plugin attempts resource identifiers `7` (internal) and `9` (public), encoding the two
decisions as `internal * 10 + public`. Its pledge says only that the plugin may use `Policy_Net`:

```bang
pledge {Policy_Net} in ...
```

That row cannot distinguish one host value from another. The reusable `install` function carries
an allowed host into an ordinary custom handler:

```bang
with (Policy_Net allowed) as net {
  connect(host) => if host == param then 1 else 0
}
```

This ordinary clause reads `param` as immutable runtime policy. A request resumes with `1` only when its host
matches the configured value; all other host values resume with `0`. Installing host `7` makes the
plugin produce `10`, while installing host `9` makes the same plugin produce `1`. The entry program
combines both observations as `10 * 100 + 1 = 1001`.

Hosts are represented by `Int` resource identifiers because that is the smallest current surface
consumer. The semantic boundary is the point: `pledge` constrains effect labels statically, while
the handler interprets operation arguments under runtime policy. This example does not claim OS
isolation or an unforgeable hostname type.

```sh
lake exe bang check examples/policy-host-allowlist/main.bang
lake exe bang run examples/policy-host-allowlist/main.bang  # 1001
```
