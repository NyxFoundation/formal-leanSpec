/-
  SHA-256 in pure Lean 4, per FIPS 180-4.

  Used by SSZ Merkleization (`hashNodes` and the zero-hash cache).
  Input/output are `ByteArray`; the 32-byte digest is also returned as `ByteArray`.

  No external dependencies; only `Init` and `Std` are used.
-/

namespace LeanSpec.Crypto.Sha256

/-- Round constants K[0..63]: first 32 bits of fractional parts of cube roots of first 64 primes. -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

/-- Initial hash values H[0..7]: first 32 bits of fractional parts of square roots of first 8 primes. -/
def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

@[inline] def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~ x) &&& z)

@[inline] def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

@[inline] def bsig0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

@[inline] def bsig1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

@[inline] def ssig0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

@[inline] def ssig1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- Read 4 bytes from `bs` starting at `off` as a big-endian `UInt32`. -/
def beU32 (bs : ByteArray) (off : Nat) : UInt32 :=
  let b0 := bs.get! off
  let b1 := bs.get! (off + 1)
  let b2 := bs.get! (off + 2)
  let b3 := bs.get! (off + 3)
  (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32

/-- Pad message per FIPS 180-4: append 0x80, zeros, then 64-bit big-endian bit length. -/
def pad (msg : ByteArray) : ByteArray := Id.run do
  let mut out := msg
  out := out.push 0x80
  let target := ((msg.size + 9 + 63) / 64) * 64
  for _ in [out.size : target - 8] do
    out := out.push 0
  let bits : UInt64 := UInt64.ofNat (msg.size * 8)
  for i in [0:8] do
    let shift : UInt64 := UInt64.ofNat ((7 - i) * 8)
    out := out.push (bits >>> shift).toUInt8
  return out

/-- Build the message schedule W[0..63] for one 64-byte block starting at `off`. -/
def schedule (bs : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for t in [0:16] do
    w := w.push (beU32 bs (off + t * 4))
  for t in [16:64] do
    let s0 := ssig0 w[t-15]!
    let s1 := ssig1 w[t-2]!
    w := w.push (w[t-16]! + s0 + w[t-7]! + s1)
  return w

/-- Compress one 512-bit block into the hash state. -/
def compress (h : Array UInt32) (w : Array UInt32) : Array UInt32 := Id.run do
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for t in [0:64] do
    let t1 := hh + bsig1 e + ch e f g + K[t]! + w[t]!
    let t2 := bsig0 a + maj a b c
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
           h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- Encode a `UInt32` as 4 big-endian bytes appended to `acc`. -/
def appendBeU32 (acc : ByteArray) (x : UInt32) : ByteArray :=
  acc
    |>.push (x >>> 24).toUInt8
    |>.push (x >>> 16).toUInt8
    |>.push (x >>> 8).toUInt8
    |>.push x.toUInt8

/-- SHA-256 of `msg` as a 32-byte `ByteArray`. -/
def sha256 (msg : ByteArray) : ByteArray := Id.run do
  let padded := pad msg
  let blocks := padded.size / 64
  let mut state := H0
  for i in [0:blocks] do
    let w := schedule padded (i * 64)
    state := compress state w
  let mut digest : ByteArray := ByteArray.empty
  for i in [0:8] do
    digest := appendBeU32 digest state[i]!
  return digest

end LeanSpec.Crypto.Sha256
