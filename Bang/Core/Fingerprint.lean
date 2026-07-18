module

meta import Bang.Core.IR
public import Bang.Core.IR

/-!
  Bang/Core/Fingerprint.lean — a reusable structural fingerprint probe for kernel `Comp` values.
  ─────────────────────────────────────────────────────────────────────────────────────────────
  This is the ONE structural fold shared by compiler-query experiments and proof export. It is
  intentionally a FINGERPRINT, not yet a persistent content address: the result is only 64 bits and
  does not domain-separate compiler/kernel versions, so a collision or a semantic-version change
  could make an on-disk cache hit unsound. Callers must expose that limitation rather than treating
  the digest as a cache key.

  The useful property this probe tests now is canonicality at the chosen boundary. `Comp` uses
  de-Bruijn indices, so source binder names and formatting are absent before this fold runs. The
  algorithm is versioned because changing constructor tags or scalar encodings changes every digest.
-/

namespace Bang.CoreFingerprint

open Bang (BinOp ClauseKey Comp Handler Val)

@[expose] public section

/-- Stable name for the exact constructor/scalar fold below. `v2` fixes v1's collapse of every
negative `Int` magnitude through `Int.toNat` and avoids truncating arbitrary `Nat` values to 64 bits
before mixing. This names an experimental fingerprint algorithm, not a cache-key guarantee. -/
def algorithm : String := "bang-comp-struct-v2-uint64"

/-- splitmix64 finalizer — an avalanche mix for the experimental 64-bit fingerprint. -/
def mix (h : UInt64) : UInt64 :=
  let z := h + 0x9e3779b97f4a7c15
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

/-- Fold a child fingerprint into the running accumulator, preserving order. -/
def step (acc child : UInt64) : UInt64 := mix (acc * 0x100000001b3 ^^^ child)

/-- Constructor/domain seeds. All uses below pass small fixed tag numbers. -/
def tag (n : Nat) : UInt64 := mix (UInt64.ofNat (n + 1))

/-- Fold the UTF-8 bytes of a canonical scalar spelling under a domain-specific seed. -/
def hashTextWith (seed : UInt64) (s : String) : UInt64 :=
  s.toUTF8.foldl (fun acc b => step acc (UInt64.ofNat b.toNat)) seed

/-- Hash an arbitrary `Nat` without first truncating it modulo 2^64. -/
def hashNat (n : Nat) : UInt64 := hashTextWith (tag 61) (toString n)

/-- Hash an arbitrary `Int`, separating sign and magnitude. `negSucc n` denotes `-(n+1)`, so every
negative literal retains its magnitude instead of collapsing through `Int.toNat`. -/
def hashInt : Int → UInt64
  | .ofNat n => step (tag 62) (hashNat n)
  | .negSucc n => step (tag 63) (hashNat (n + 1))

/-- Hash a string scalar (operation ids and `wrong` messages), preserving its UTF-8 byte order. -/
def hashStr (s : String) : UInt64 := hashTextWith (tag 60) s

/-- Hash a primitive binary operator under distinct constructor tags. -/
def hashBinOp : BinOp → UInt64
  | .add => tag 40 | .sub => tag 41 | .mul => tag 42
  | .div => tag 43 | .lt => tag 44 | .eq => tag 45

/-- Hash an operation name together with its custom-clause update mode. -/
def hashClauseKey : ClauseKey → UInt64
  | .plain op => step (tag 34) (hashStr op)
  | .updating op => step (tag 35) (hashStr op)

mutual
/-- Structurally fingerprint a kernel value. -/
partial def hashVal : Val → UInt64
  | .vunit      => tag 0
  | .vint n     => step (tag 1) (hashInt n)
  | .vvar i     => step (tag 2) (hashNat i)
  | .vcap n l   => step (step (tag 3) (hashNat n)) (hashNat l)
  | .vthunk c   => step (tag 4) (hashComp c)
  | .inl v      => step (tag 5) (hashVal v)
  | .inr v      => step (tag 6) (hashVal v)
  | .pair a b   => step (step (tag 7) (hashVal a)) (hashVal b)
  | .fold v     => step (tag 8) (hashVal v)
/-- Structurally fingerprint a kernel computation. -/
partial def hashComp : Comp → UInt64
  | .ret v          => step (tag 10) (hashVal v)
  | .letC m n       => step (step (tag 11) (hashComp m)) (hashComp n)
  | .force v        => step (tag 12) (hashVal v)
  | .lam m          => step (tag 13) (hashComp m)
  | .app m v        => step (step (tag 14) (hashComp m)) (hashVal v)
  | .perform c op v => step (step (step (tag 15) (hashVal c)) (hashStr op)) (hashVal v)
  | .handle h m     => step (step (tag 16) (hashHandler h)) (hashComp m)
  | .case v n1 n2   => step (step (step (tag 17) (hashVal v)) (hashComp n1)) (hashComp n2)
  | .split v n      => step (step (tag 18) (hashVal v)) (hashComp n)
  | .unfold v       => step (tag 19) (hashVal v)
  | .binop op v w   => step (step (step (tag 20) (hashBinOp op)) (hashVal v)) (hashVal w)
  | .oom            => tag 21
  | .wrong s        => step (tag 22) (hashStr s)
/-- Structurally fingerprint a kernel handler. -/
partial def hashHandler : Handler → UInt64
  | .state l v        => step (step (tag 30) (hashNat l)) (hashVal v)
  | .throws l         => step (tag 31) (hashNat l)
  | .transaction l vs => vs.foldl (fun acc v => step acc (hashVal v)) (step (tag 32) (hashNat l))
  | .custom l p cls   =>
      cls.foldl (fun acc (key, c) => step (step acc (hashClauseKey key)) (hashComp c))
        (step (step (tag 33) (hashNat l)) (hashVal p))
end

/-- One lowercase hexadecimal digit for a nibble. -/
def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

/-- Render a `UInt64` as exactly 16 lowercase hexadecimal digits. -/
def toHex16 (u : UInt64) : String :=
  let rec go (fuel : Nat) (rest : UInt64) (acc : String) : String :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
        go fuel (rest >>> 4) (String.singleton (hexDigit (rest &&& 0xf).toNat) ++ acc)
  go 16 u ""

/-- Experimental structural fingerprint of an elaborated `Comp`. Not collision-safe for storage. -/
def fingerprint (c : Comp) : String := toHex16 (hashComp c)

-- Scalar falsification poles: v1 collapsed negative magnitudes and truncated large `Nat`s first.
#guard fingerprint (.ret (.vint (-1))) != fingerprint (.ret (.vint (-2)))
#guard fingerprint (.ret (.vvar 0)) != fingerprint (.ret (.vvar (2 ^ 64)))

-- Shape and elementary semantic discrimination at the kernel boundary.
#guard fingerprint (.ret (.vint 1)) != fingerprint (.ret (.vint 2))
#guard (fingerprint (.ret (.vint 1))).length == 16

end -- public section

end Bang.CoreFingerprint
