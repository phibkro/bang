/-
  scratch/calc95/StepProbe.lean — issue #95 fuel-vs-loop probe (SCRATCH, non-proof-bearing).

  Re-implements `Bang.CalcVM.exec` as a STEP-COUNTING variant `execCount` that
  returns (steps-consumed, terminal?), so we can measure the machine-step cost of
  the compiled path on the "hanging" calc inputs vs the fast ones.

  It reuses the machine's REAL `compile`/`stateUpdate`/`txnUpdate`/`customUpdate`/
  `unwindFind` verbatim — the ONLY change is that each recursive call increments a
  counter, so the step count is faithful to the proof-bearing `exec` (same control
  flow, same fuel decrement). Verdict logic in Main below.

  This does NOT touch AbstractMachine.lean; it is a leaf reader.
-/
import Bang.Backend.AbstractMachine
import Bang.Frontend.TypeCheck
import Bang.Frontend.Surface

open Bang
open Bang.CalcVM
open Bang.Surface

namespace Hang95

mutual
/-- Structural size of a `Val` (node count). -/
partial def vsize : Val → Nat
  | .vunit | .vint _ | .vvar _ | .vcap _ _ => 1
  | .vthunk c => 1 + csize c
  | .inl v | .inr v | .fold v => 1 + vsize v
  | .pair a b => 1 + vsize a + vsize b
/-- Structural size of a `Comp` (node count). -/
partial def csize : Comp → Nat
  | .ret v | .force v => 1 + vsize v
  | .letC m n => 1 + csize m + csize n
  | .lam m => 1 + csize m
  | .app m v => 1 + csize m + vsize v
  | .perform c _ v => 1 + vsize c + vsize v
  | .handle _ m => 1 + csize m
  | .case v n1 n2 => 1 + vsize v + csize n1 + csize n2
  | .split v n => 1 + vsize v + csize n
  | .unfold v => 1 + vsize v
  | .binop _ v w => 1 + vsize v + vsize w
  | .oom => 1
  | .wrong _ => 1
end

/-- Step-counting mirror of `Bang.CalcVM.exec`. Returns `(steps, some finalStack)`
on termination or `(steps, none)` on fuel-exhaustion. `steps` = the number of
fuel-decrementing transitions actually taken. Identical control flow to `exec`. -/
def execCount : Nat → Nat → Nat → Code → Stack → HStack → (Nat × Option Stack)
  | 0,          n, _, _,                  _, _  => (n, none)
  | Nat.succ _, n, _, [],                 s, _  => (n, some s)
  | Nat.succ f, n, g, Instr.RET v :: c,   s, hs => execCount f (n+1) g c (.ret v :: s) hs
  | Nat.succ f, n, g, Instr.LAMI M :: c,  s, hs => execCount f (n+1) g c (.lam M :: s) hs
  | Nat.succ f, n, g, Instr.SUBST N :: c, s, hs =>
      match s with
      | .ret v :: s' => execCount f (n+1) g (compile (Comp.subst v N) c) s' hs
      | _            => (n, none)
  | Nat.succ f, n, g, Instr.APP v :: c, s, hs =>
      match s with
      | .lam N :: s' => execCount f (n+1) g (compile (Comp.subst v N) c) s' hs
      | _            => (n, none)
  | Nat.succ f, n, g, Instr.HANDLE h M :: c, s, hs =>
      let id := g
      execCount f (n+1) (g+1) (compile (Comp.subst (.vcap id h.label) M) (Instr.UNMARK :: c)) s
        ({ id := id, handler := h, savedCode := c, savedStack := s } :: hs)
  | Nat.succ f, n, g, Instr.UNMARK :: c, s, hs =>
      match hs with
      | _ :: hs' => execCount f (n+1) g c s hs'
      | []       => (n, none)
  | Nat.succ f, n, g, Instr.THROW nn op v :: _, _, hs =>
      match unwindFind nn op hs with
      | some (c', s', hs') => execCount f (n+1) g c' (.ret v :: s') hs'
      | none               => (n, none)
  | Nat.succ f, n, g, Instr.OP nn op v :: c, s, hs =>
      match stateUpdate nn op v hs with
      | some (r, hs') => execCount f (n+1) g c (.ret r :: s) hs'
      | none =>
          match txnUpdate nn op v hs with
          | some (r, hs') => execCount f (n+1) g c (.ret r :: s) hs'
          | none =>
              match customUpdate nn op v hs with
              | some (body, hs') => execCount f (n+1) g (compile body c) s hs'
              | none =>
                  match unwindFind nn op hs with
                  | some (c', s', hs') => execCount f (n+1) g c' (.ret v :: s') hs'
                  | none               => (n, none)
  | Nat.succ f, n, g, Instr.CASE w N₁ N₂ :: c, s, hs =>
      match w with
      | .inl v => execCount f (n+1) g (compile (Comp.subst v N₁) c) s hs
      | .inr v => execCount f (n+1) g (compile (Comp.subst v N₂) c) s hs
      | _      => (n, none)
  | Nat.succ f, n, g, Instr.SPLIT w N :: c, s, hs =>
      match w with
      | .pair v u => execCount f (n+1) g (compile (Comp.subst v (Comp.subst (Val.shift u) N)) c) s hs
      | _         => (n, none)

/-- Size of one `Instr` (the residual `Comp`/`Val` it carries — this is what a
`compile`/`subst` at that instruction must traverse). -/
def isize : Instr → Nat
  | .RET v      => 1 + vsize v
  | .LAMI m     => 1 + csize m
  | .SUBST n    => 1 + csize n
  | .APP v      => 1 + vsize v
  | .HANDLE _ m => 1 + csize m
  | .UNMARK     => 1
  | .THROW _ _ v => 1 + vsize v
  | .OP _ _ v   => 1 + vsize v
  | .CASE v a b => 1 + vsize v + csize a + csize b
  | .SPLIT v a  => 1 + vsize v + csize a

def codeSize (c : Code) : Nat := c.foldl (fun acc i => acc + isize i) 0

/-- Instrumented exec: tracks (steps, maxSubstTermSize, maxCodeSize, totalSubstWork).
`maxSubstTermSize` = the largest `csize (Comp.subst v N)` handed to `compile` at any
SUBST/APP/OP-custom step; `totalSubstWork` accumulates those sizes (a proxy for total
substitution+compile work — the suspected quadratic). -/
partial def execTrack : Nat → Nat → Nat → Nat → Nat → Nat → Code → Stack → HStack →
    (Nat × Nat × Nat × Nat × Option Stack)
  | 0,          steps, mx, mxc, tot, _, _,   _, _ => (steps, mx, mxc, tot, none)
  | Nat.succ _, steps, mx, mxc, tot, _, [],  s, _ => (steps, mx, mxc, tot, some s)
  | Nat.succ f, steps, mx, mxc, tot, g, code, s, hs =>
    let mxc := Nat.max mxc (codeSize code)
    match code with
    | Instr.RET v :: c   => execTrack f (steps+1) mx mxc tot g c (.ret v :: s) hs
    | Instr.LAMI m :: c  => execTrack f (steps+1) mx mxc tot g c (.lam m :: s) hs
    | Instr.SUBST n :: c =>
        match s with
        | .ret v :: s' =>
            let sz := csize (Comp.subst v n)
            execTrack f (steps+1) (Nat.max mx sz) mxc (tot+sz) g (compile (Comp.subst v n) c) s' hs
        | _ => (steps, mx, mxc, tot, none)
    | Instr.APP v :: c =>
        match s with
        | .lam n :: s' =>
            let sz := csize (Comp.subst v n)
            execTrack f (steps+1) (Nat.max mx sz) mxc (tot+sz) g (compile (Comp.subst v n) c) s' hs
        | _ => (steps, mx, mxc, tot, none)
    | Instr.HANDLE h m :: c =>
        let id := g
        let body := Comp.subst (.vcap id h.label) m
        let sz := csize body
        execTrack f (steps+1) (Nat.max mx sz) mxc (tot+sz) (g+1)
          (compile body (Instr.UNMARK :: c)) s
          ({ id := id, handler := h, savedCode := c, savedStack := s } :: hs)
    | Instr.UNMARK :: c =>
        match hs with
        | _ :: hs' => execTrack f (steps+1) mx mxc tot g c s hs'
        | []       => (steps, mx, mxc, tot, none)
    | Instr.THROW nn op v :: _ =>
        match unwindFind nn op hs with
        | some (c', s', hs') => execTrack f (steps+1) mx mxc tot g c' (.ret v :: s') hs'
        | none               => (steps, mx, mxc, tot, none)
    | Instr.OP nn op v :: c =>
        match stateUpdate nn op v hs with
        | some (r, hs') => execTrack f (steps+1) mx mxc tot g c (.ret r :: s) hs'
        | none =>
          match txnUpdate nn op v hs with
          | some (r, hs') => execTrack f (steps+1) mx mxc tot g c (.ret r :: s) hs'
          | none =>
            match customUpdate nn op v hs with
            | some (body, hs') =>
                let sz := csize body
                execTrack f (steps+1) (Nat.max mx sz) mxc (tot+sz) g (compile body c) s hs'
            | none =>
              match unwindFind nn op hs with
              | some (c', s', hs') => execTrack f (steps+1) mx mxc tot g c' (.ret v :: s') hs'
              | none               => (steps, mx, mxc, tot, none)
    | Instr.CASE w n1 n2 :: c =>
        match w with
        | .inl v => let b := Comp.subst v n1; let sz := csize b
                    execTrack f (steps+1) (Nat.max mx sz) mxc (tot+sz) g (compile b c) s hs
        | .inr v => let b := Comp.subst v n2; let sz := csize b
                    execTrack f (steps+1) (Nat.max mx sz) mxc (tot+sz) g (compile b c) s hs
        | _      => (steps, mx, mxc, tot, none)
    | Instr.SPLIT w n :: c =>
        match w with
        | .pair v u => let b := Comp.subst v (Comp.subst (Val.shift u) n); let sz := csize b
                       execTrack f (steps+1) (Nat.max mx sz) mxc (tot+sz) g (compile b c) s hs
        | _         => (steps, mx, mxc, tot, none)
    | [] => (steps, mx, mxc, tot, some s)

def instrTag : Instr → String
  | .RET _ => "RET" | .LAMI _ => "LAMI" | .SUBST _ => "SUBST" | .APP _ => "APP"
  | .HANDLE _ _ => "HANDLE" | .UNMARK => "UNMARK" | .THROW _ _ _ => "THROW"
  | .OP _ _ _ => "OP" | .CASE _ _ _ => "CASE" | .SPLIT _ _ => "SPLIT"

/-- Trace codeSize + head-instr at each step (bounded). Returns list of (step, codeSize, tag). -/
partial def execTrace : Nat → Nat → Nat → Code → Stack → HStack → List (Nat × Nat × String)
  | 0, _, _, _, _, _ => []
  | Nat.succ f, i, g, code, s, hs =>
    match code with
    | [] => []
    | instr :: _ =>
      let entry := (i, codeSize code, instrTag instr)
      let rest :=
        match code with
        | Instr.RET v :: c   => execTrace f (i+1) g c (.ret v :: s) hs
        | Instr.LAMI m :: c  => execTrace f (i+1) g c (.lam m :: s) hs
        | Instr.SUBST n :: c =>
            match s with
            | .ret v :: s' => execTrace f (i+1) g (compile (Comp.subst v n) c) s' hs
            | _ => []
        | Instr.APP v :: c =>
            match s with
            | .lam n :: s' => execTrace f (i+1) g (compile (Comp.subst v n) c) s' hs
            | _ => []
        | Instr.HANDLE h m :: c =>
            let id := g
            execTrace f (i+1) (g+1) (compile (Comp.subst (.vcap id h.label) m) (Instr.UNMARK :: c)) s
              ({ id := id, handler := h, savedCode := c, savedStack := s } :: hs)
        | Instr.UNMARK :: c => match hs with | _ :: hs' => execTrace f (i+1) g c s hs' | [] => []
        | Instr.THROW nn op v :: _ =>
            match unwindFind nn op hs with
            | some (c', s', hs') => execTrace f (i+1) g c' (.ret v :: s') hs' | none => []
        | Instr.OP nn op v :: c =>
            match stateUpdate nn op v hs with
            | some (r, hs') => execTrace f (i+1) g c (.ret r :: s) hs'
            | none => match txnUpdate nn op v hs with
              | some (r, hs') => execTrace f (i+1) g c (.ret r :: s) hs'
              | none => match customUpdate nn op v hs with
                | some (body, hs') => execTrace f (i+1) g (compile body c) s hs'
                | none => match unwindFind nn op hs with
                  | some (c', s', hs') => execTrace f (i+1) g c' (.ret v :: s') hs' | none => []
        | Instr.CASE w n1 n2 :: c =>
            match w with
            | .inl v => execTrace f (i+1) g (compile (Comp.subst v n1) c) s hs
            | .inr v => execTrace f (i+1) g (compile (Comp.subst v n2) c) s hs
            | _ => []
        | Instr.SPLIT w n :: c =>
            match w with
            | .pair v u => execTrace f (i+1) g (compile (Comp.subst v (Comp.subst (Val.shift u) n)) c) s hs
            | _ => []
        | [] => []
      entry :: rest

/-- Resolve+lower ONE calc input into a `Comp`, reusing the calc modules by INLINING
their sources. To keep the probe self-contained we read the 4 module files + build a
tiny entry `Prog` via the same `mergeModules` the CLI uses. -/
def lowerCalcInput (astSrc lexSrc parserSrc evalSrc entrySrc : String) : Except String Comp := do
  let astP     ← Bang.Surface.parseProg astSrc     |>.mapError (s!"Ast: " ++ ·)
  let lexP     ← Bang.Surface.parseProg lexSrc     |>.mapError (s!"Lexer: " ++ ·)
  let parserP  ← Bang.Surface.parseProg parserSrc  |>.mapError (s!"Parser: " ++ ·)
  let evalP    ← Bang.Surface.parseProg evalSrc    |>.mapError (s!"Eval: " ++ ·)
  let entryP   ← Bang.Surface.parseProg entrySrc   |>.mapError (s!"entry: " ++ ·)
  -- dependency-first order: Ast, Lexer, Parser, Eval  (Parser imports Ast/Lexer; Eval imports Ast)
  let resolved : List (String × Bang.Surface.Prog) :=
    [("Ast", astP), ("Lexer", lexP), ("Parser", parserP), ("Eval", evalP)]
  let merged ← Bang.TypeCheck.mergeModules resolved entryP
  -- program mode: body := main
  let merged2 :=
    if merged.decls.any (fun d => match d with
        | .letD n _ _ | .letRecD n _ _ => n == "main"
        | _ => false)
    then { merged with body := Surf.var "main", isLibrary := false }
    else merged
  Bang.TypeCheck.checkAndLowerProg merged2

def compiledFuel : Nat := 20000000

def runComp95 (c : Comp) : IO UInt32 := do
  let code := compile c []
  let initCodeSize := codeSize code
  let (steps, mx, mxc, tot, res) := execTrack compiledFuel 0 0 0 0 0 code [] []
  IO.println s!"initCompiledCodeSize={initCodeSize}"
  IO.println s!"steps={steps} maxSubstTermSize={mx} maxCodeSize={mxc} totalSubstWork={tot}"
  match res with
  | some [.ret _] => IO.println s!"TERMINATED value=ok"; pure 0
  | some _        => IO.println s!"TERMINATED (non-value terminal)"; pure 0
  | none          => IO.println s!"FUEL-EXHAUSTED (>= {compiledFuel})"; pure 2

def main (args : List String) : IO UInt32 := do
  -- args: astFile lexFile parserFile evalFile entryFile   OR   --single file.bang
  match args with
  | ["--single", f] =>
    let src ← IO.FS.readFile f
    match Bang.TypeCheck.checkAndLower src with
    | .error (m, _) => IO.eprintln s!"lower error: {m}"; pure 1
    | .ok c => runComp95 c
  | [astF, lexF, parserF, evalF, entryF] =>
    let astSrc    ← IO.FS.readFile astF
    let lexSrc    ← IO.FS.readFile lexF
    let parserSrc ← IO.FS.readFile parserF
    let evalSrc   ← IO.FS.readFile evalF
    let entrySrc  ← IO.FS.readFile entryF
    match lowerCalcInput astSrc lexSrc parserSrc evalSrc entrySrc with
    | .error e => IO.eprintln s!"lower error: {e}"; pure 1
    | .ok c =>
      let code := compile c []
      let initCodeSize := codeSize code
      let (steps, mx, mxc, tot, res) := execTrack compiledFuel 0 0 0 0 0 code [] []
      IO.println s!"initCompiledCodeSize={initCodeSize}"
      IO.println s!"steps={steps} maxSubstTermSize={mx} maxCodeSize={mxc} totalSubstWork={tot}"
      -- also print a codeSize trace: run a bounded execTrace collecting (step,codeSize) pairs
      let trace := execTrace 2000 0 0 code [] []
      IO.println s!"codeSizeTrace(first {trace.length}):"
      for (i, sz, tag) in trace do
        if i % 20 == 0 || sz > 5000 then IO.println s!"  step={i} codeSize={sz} instr={tag}"
      match res with
      | some [.ret _] => IO.println s!"TERMINATED value=ok"; pure 0
      | some _        => IO.println s!"TERMINATED (non-value terminal)"; pure 0
      | none          => IO.println s!"FUEL-EXHAUSTED (>= {compiledFuel})"; pure 2
  | _ => IO.eprintln "usage: stepprobe Ast Lexer Parser Eval entry"; pure 1

end Hang95

def main (args : List String) : IO UInt32 := Hang95.main args
