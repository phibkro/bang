;; ◊5 engine probe (ADR-0035 / OPEN_QUESTIONS Q9) — the run-the-real-journey artifact.
;;
;; A minimal stack-switching GENERATOR: a continuation that SUSPENDs once with a
;; payload (42), which the caller RESUMEs; the resumed body returns 7. main sums
;; them → 49. This is the tracer/generator effect (ADR-0025 resumptive state):
;; suspend/resume, NOT throws→resume_throw (the latter is Wasmtime #10248, unlanded).
;;
;; Shape = the CURRENT WebAssembly stack-switching Explainer (NOT OOPSLA'23
;; `(tag $e $h)`), matching the ◊5 `Wasmfx.Instr` lowering:
;;   markH  ≙ the handler boundary / cont.new + the resume's (on $tag $label)
;;   opH    ≙ suspend $tag   (resumptive perform)
;;   resume continues the captured continuation in place (one-shot, shape (A))
;;
;; RUN (x86_64 Linux, wasmtime ≥ 44.0.1):
;;   wasmtime run -W stack-switching=y,function-references=y,gc=y,exceptions=y \
;;     --invoke main test/wasmfx/generator.wat        ⟹ 49
;; (exceptions=y is required only because the tag machinery shares that proposal's
;; feature gate — the generator path itself uses no exception-control.)
(module
  (type $ft (func (result i32)))            ;; the function the continuation runs
  (type $ct (cont $ft))                     ;; continuation type
  (tag $yield (param i32))                  ;; the suspend tag (carries the yielded i32)
  (elem declare func $gen)                  ;; required for `ref.func $gen`

  ;; generator body: yield 42, then (on resume) return 7
  (func $gen (result i32)
    (i32.const 42)
    (suspend $yield)
    (i32.const 7))

  (func (export "main") (result i32)
    (local $k (ref null $ct))
    (local $acc i32)
    ;; first resume: run the continuation, handling $yield → $on_yield
    (block $on_yield (result i32 (ref $ct))
      (resume $ct (on $yield $on_yield)
        (cont.new $ct (ref.func $gen)))
      (return))                             ;; (no-suspend path: not taken here)
    ;; $on_yield: operand stack = [yielded:i32, k:contref]
    (local.set $k)
    (local.set $acc)                        ;; acc := 42
    ;; second resume: the continuation returns 7 with no further suspend
    (block $on_yield2 (result i32 (ref $ct))
      (local.set $acc (i32.add (local.get $acc)
        (resume $ct (on $yield $on_yield2) (local.get $k))))
      (return (local.get $acc)))            ;; 42 + 7 = 49
    (drop) (unreachable))
)
