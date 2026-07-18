# stateful-quota

An updating custom handler owns a one-request quota. The handled program keeps one stable `Quota`
capability and calls it twice; it never receives or returns the quota state.

```bang
with (Quota 1) as quota {
  update connect(host) => (param, 0)
}
```

`update` marks the clause as state-transitioning. Its value pair is
`(resumeValue, nextParam)`: the first call resumes with `1` and atomically installs `0`; the second
call therefore resumes with `0`. The program combines the observations as `1 * 10 + 0 = 10`.

```sh
lake exe bang check examples/stateful-quota/main.bang
lake exe bang run examples/stateful-quota/main.bang  # 10
```
