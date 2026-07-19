module

/-!
  Bang/Core/SHA256.lean — a small pure SHA-256 implementation for artifact integrity.
  ───────────────────────────────────────────────────────────────────────────────
  This module owns no cache or trust decision. It implements FIPS 180-4 SHA-256 over UTF-8 bytes so
  Core artifact contracts can use a collision-resistant address without shelling out or importing an
  edge-layer dependency. Standard single- and multi-block vectors below guard the implementation.
-/

namespace Bang.SHA256

@[expose] public section

def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

structure State where
  h0 : UInt32
  h1 : UInt32
  h2 : UInt32
  h3 : UInt32
  h4 : UInt32
  h5 : UInt32
  h6 : UInt32
  h7 : UInt32

def initial : State :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

def rotr (x : UInt32) (n : Nat) : UInt32 :=
  (x >>> UInt32.ofNat n) ||| (x <<< UInt32.ofNat (32 - n))

def choose (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((x ^^^ 0xffffffff) &&& z)

def majority (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

def padded (input : ByteArray) : ByteArray := Id.run do
  let bitLength := UInt64.ofNat input.size * 8
  let mut out := input.push 0x80
  let zeroCount := (56 + 64 - out.size % 64) % 64
  for _ in [0:zeroCount] do
    out := out.push 0
  for i in [0:8] do
    let shift := (7 - i) * 8
    out := out.push (UInt8.ofNat ((bitLength >>> UInt64.ofNat shift).toNat))
  return out

def wordAt (bytes : ByteArray) (offset : Nat) : UInt32 :=
  (UInt32.ofNat bytes[offset]!.toNat <<< 24) |||
  (UInt32.ofNat bytes[offset + 1]!.toNat <<< 16) |||
  (UInt32.ofNat bytes[offset + 2]!.toNat <<< 8) |||
  UInt32.ofNat bytes[offset + 3]!.toNat

def schedule (bytes : ByteArray) (offset : Nat) : Array UInt32 := Id.run do
  let mut words := Array.replicate 64 0
  for i in [0:16] do
    words := words.set! i (wordAt bytes (offset + i * 4))
  for i in [16:64] do
    let next := smallSigma1 words[i - 2]! + words[i - 7]! +
      smallSigma0 words[i - 15]! + words[i - 16]!
    words := words.set! i next
  return words

def compress (state : State) (bytes : ByteArray) (offset : Nat) : State := Id.run do
  let words := schedule bytes offset
  let mut a := state.h0
  let mut b := state.h1
  let mut c := state.h2
  let mut d := state.h3
  let mut e := state.h4
  let mut f := state.h5
  let mut g := state.h6
  let mut h := state.h7
  for i in [0:64] do
    let t1 := h + bigSigma1 e + choose e f g + k[i]! + words[i]!
    let t2 := bigSigma0 a + majority a b c
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return ⟨state.h0 + a, state.h1 + b, state.h2 + c, state.h3 + d,
    state.h4 + e, state.h5 + f, state.h6 + g, state.h7 + h⟩

def digestState (input : ByteArray) : State := Id.run do
  let bytes := padded input
  let mut state := initial
  for block in [0:bytes.size / 64] do
    state := compress state bytes (block * 64)
  return state

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

def hexWord (word : UInt32) : String :=
  let rec go : Nat → UInt32 → String → String
    | 0, _, acc => acc
    | fuel + 1, rest, acc =>
        go fuel (rest >>> 4) (String.singleton (hexDigit (rest &&& 0xf).toNat) ++ acc)
  go 8 word ""

/-- SHA-256 of raw bytes as exactly 64 lowercase hexadecimal digits. -/
def hashBytes (input : ByteArray) : String :=
  let s := digestState input
  hexWord s.h0 ++ hexWord s.h1 ++ hexWord s.h2 ++ hexWord s.h3 ++
    hexWord s.h4 ++ hexWord s.h5 ++ hexWord s.h6 ++ hexWord s.h7

/-- SHA-256 of a string's UTF-8 bytes as exactly 64 lowercase hexadecimal digits. -/
def hash (input : String) : String := hashBytes input.toUTF8

-- FIPS/NIST vectors: empty, one short block, and a message spanning two padded blocks.
#guard hash "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard hash "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

end

end Bang.SHA256
