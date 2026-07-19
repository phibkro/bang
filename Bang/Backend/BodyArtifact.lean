module

meta import Bang.Core.CompCodec
meta import Bang.Backend.AbstractMachine
meta import Bang.Backend.EnvMachine
public import Bang.Core.CompCodec
public import Bang.Backend.AbstractMachine
public import Bang.Backend.EnvMachine

/-!
  Bang/Backend/BodyArtifact.lean — the first real consumer of structural `Comp` artifacts.
  ──────────────────────────────────────────────────────────────────────────────────────
  This intentionally contains no second compiler or evaluator. It decodes through the shared strict
  codec, then calls the unchanged calculated VM compiler or environment-machine runner. Successful
  consumption therefore establishes that the interchange format reconstructs executable kernel code.

  It does NOT establish that arbitrary external bytes are well typed. The current producer gets its
  term from `checkAndLowerProgWithEffects`; an independent validator/certificate remains future work.
-/

namespace Bang.BodyArtifactConsumer

@[expose] public section

/-- Structurally decode an artifact and compile it with the existing calculated VM compiler. -/
def compile (artifact : String) : Except String Bang.CalcVM.Code := do
  let comp ← Bang.CompCodec.decodeArtifact artifact
  pure (Bang.CalcVM.compile comp [])

/-- Structurally decode an artifact and run it with the existing environment machine. -/
def run (fuel : Nat) (artifact : String) : Except String (Bang.Result Bang.Val) := do
  let comp ← Bang.CompCodec.decodeArtifact artifact
  pure (Bang.EnvMachine.runE fuel comp)

/-- Verify a collision-resistant envelope address before compiling through the existing backend. -/
def compileVerified (artifact : String) (stableRelocations : List (String × Nat))
    (claimedAddress : String) : Except String Bang.CalcVM.Code := do
  let comp ← Bang.CompCodec.verifyAddress artifact stableRelocations claimedAddress
  pure (Bang.CalcVM.compile comp [])

/-- Verify a collision-resistant envelope address before running through the existing backend. -/
def runVerified (fuel : Nat) (artifact : String) (stableRelocations : List (String × Nat))
    (claimedAddress : String) : Except String (Bang.Result Bang.Val) := do
  let comp ← Bang.CompCodec.verifyAddress artifact stableRelocations claimedAddress
  pure (Bang.EnvMachine.runE fuel comp)

private def pureSample : Bang.Comp :=
  .letC (.ret (.vint 40)) (.binop .add (.vvar 0) (.vint 2))

private def effectSample : Bang.Comp :=
  .handle (.state 4 (.vint 7)) (.perform (.vvar 0) "get" .vunit)

-- Both a pure binder and a canonical-labelled handler survive bytes and the unchanged backend.
#guard match run 100 (Bang.CompCodec.encodeArtifact pureSample) with
  | .ok (.done (.vint 42)) => true
  | _ => false

#guard match run 100 (Bang.CompCodec.encodeArtifact effectSample) with
  | .ok (.done (.vint 7)) => true
  | _ => false

-- The compile consumer emits real code, while malformed bytes never reach the compiler.
#guard !(match compile (Bang.CompCodec.encodeArtifact pureSample) with
  | .ok [] => true
  | _ => false)

#guard match compile "[\"bang-core-comp-json-v1\",[\"future\"]]" with
  | .error _ => true
  | .ok _ => false

private def effectArtifact := Bang.CompCodec.encodeArtifact effectSample
private def effectRows : List (String × Nat) := [("Lib_StateLike", 4)]
private def effectAddress := Bang.CompCodec.address effectArtifact effectRows

-- The verified consumer reaches the same backend only after address, bytes, and stable rows agree.
#guard match effectAddress with
  | .ok address => match runVerified 100 effectArtifact effectRows address with
      | .ok (.done (.vint 7)) => true
      | _ => false
  | .error _ => false

#guard match effectAddress with
  | .ok address => match compileVerified effectArtifact effectRows (address ++ "0") with
      | .error _ => true
      | .ok _ => false
  | .error _ => false

end


end Bang.BodyArtifactConsumer
