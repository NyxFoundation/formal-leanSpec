/-
  SSZ bitfield types.

  Mirrors `src/lean_spec/types/bitfields.py`:

  - `BaseBitvector` → `Bitvector n`: exactly `n` bits, packed LSB-first into
    `(n + 7) / 8` bytes; high bits in the last byte must be zero.

  - `BaseBitlist`   → `Bitlist limit`: 0..`limit` bits, packed LSB-first, with
    a sentinel `1` bit appended one position past the last data bit. Empty
    bitlists encode as `0x01`. Decode locates the sentinel as the highest
    set bit and treats every bit below it as data.

  Both types use `Array Bool` as their in-memory representation. This makes
  the encoder and decoder straightforward and gives a structural target for
  round-trip proofs.
-/

import LeanSpec.Types.Base

namespace LeanSpec.Types

/-- Number of bytes required to pack `n` bits LSB-first. -/
@[inline] def bitsToBytes (n : Nat) : Nat := (n + 7) / 8

/-- Pack `bits` LSB-first into a `ByteArray` of `bitsToBytes bits.size` bytes. -/
def packBits (bits : Array Bool) : ByteArray := Id.run do
  let nBytes := bitsToBytes bits.size
  let mut out : ByteArray := ByteArray.empty
  for byteIdx in [0:nBytes] do
    let mut b : UInt8 := 0
    for j in [0:8] do
      let bitIdx := byteIdx * 8 + j
      if hLt : bitIdx < bits.size then
        if bits[bitIdx]'hLt then
          b := b ||| ((1 : UInt8) <<< j.toUInt8)
    out := out.push b
  return out

/-- Unpack the first `nBits` bits from `bs`, LSB-first. -/
def unpackBits (bs : ByteArray) (nBits : Nat) : Array Bool := Id.run do
  let mut out : Array Bool := Array.mkEmpty nBits
  for i in [0:nBits] do
    let byteIdx := i / 8
    let bitInByte := i % 8
    let b : UInt8 := if byteIdx < bs.size then bs.get! byteIdx else 0
    let bit := (b >>> bitInByte.toUInt8) &&& 1 != 0
    out := out.push bit
  return out

/-- Are all bits at positions `≥ start` in `b` zero? Used to validate Bitvector tail. -/
def topBitsZero (b : UInt8) (start : Nat) : Bool :=
  if start ≥ 8 then true
  else (b >>> start.toUInt8) = 0

/-- Locate the position of the highest set bit in `bs`, or `none` if all zero. -/
def findHighestSetBit (bs : ByteArray) : Option Nat := Id.run do
  if bs.size = 0 then return none
  let mut byteIdx : Nat := bs.size - 1
  let mut found : Option Nat := none
  let mut keepGoing : Bool := true
  while keepGoing do
    let b := bs.get! byteIdx
    if b ≠ 0 then
      let mut bitPos : Nat := 0
      let mut bitFound : Bool := false
      for j in [0:8] do
        let candidate : Nat := 7 - j
        if !bitFound && ((b >>> candidate.toUInt8) &&& 1 ≠ 0) then
          bitPos := candidate
          bitFound := true
      found := some (byteIdx * 8 + bitPos)
      keepGoing := false
    else if byteIdx = 0 then
      keepGoing := false
    else
      byteIdx := byteIdx - 1
  return found

/-- Fixed-length bitvector. -/
structure Bitvector (n : Nat) where
  bits : Array Bool
  deriving Inhabited

namespace Bitvector

variable {n : Nat}

def beq (a b : Bitvector n) : Bool := a.bits = b.bits

instance : BEq (Bitvector n) := ⟨beq⟩

instance : SSZType (Bitvector n) where
  isFixedSize := true
  fixedByteLength := bitsToBytes n
  serialize x out := out ++ packBits x.bits
  deserialize bs off sz :=
    let expected := bitsToBytes n
    if sz != expected then
      .error (.sizeMismatch expected sz)
    else if off + sz > bs.size then
      .error (.underflow sz (bs.size - off))
    else
      let slice := bs.extract off (off + sz)
      let bitsInLast : Nat := n % 8
      let lastIdx : Nat := if expected = 0 then 0 else expected - 1
      let lastByte : UInt8 := if expected = 0 then 0 else slice.get! lastIdx
      if expected > 0 && bitsInLast ≠ 0 && !topBitsZero lastByte bitsInLast then
        .error .invalidBitvectorTail
      else
        .ok ⟨unpackBits slice n⟩

end Bitvector

/-- Variable-length bitlist bounded by `limit` bits. -/
structure Bitlist (limit : Nat) where
  bits : Array Bool
  deriving Inhabited

namespace Bitlist

variable {limit : Nat}

def beq (a b : Bitlist limit) : Bool := a.bits = b.bits

instance : BEq (Bitlist limit) := ⟨beq⟩

/-- Encoded bytes: data bits LSB-first, then sentinel `1` at position `bits.size`. -/
def encodeBitlist (bits : Array Bool) : ByteArray :=
  packBits (bits.push true)

instance : SSZType (Bitlist limit) where
  isFixedSize := false
  fixedByteLength := 0
  serialize x out := out ++ encodeBitlist x.bits
  deserialize bs off sz :=
    if sz = 0 then
      .error .invalidBitlistSentinel
    else if off + sz > bs.size then
      .error (.underflow sz (bs.size - off))
    else
      let slice := bs.extract off (off + sz)
      match findHighestSetBit slice with
      | none => .error .invalidBitlistSentinel
      | some pos =>
        if pos > limit then
          .error (.tooManyElements limit pos)
        else
          .ok ⟨unpackBits slice pos⟩

end Bitlist

end LeanSpec.Types
