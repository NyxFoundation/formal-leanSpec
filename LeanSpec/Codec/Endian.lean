/-
  Little-endian byte readers and writers used by every fixed-size SSZ scalar.

  These helpers are extracted because the same pattern is used by `Uint`,
  variable-length offset tables in `Collection` and `Container`, and the
  internal `Nat → 32-byte LE` conversion required by `mixInLength` and
  `mixInSelector`. Centralising them keeps the per-type encoders trivial.
-/

namespace LeanSpec.Codec.Endian

/-- Append the low byte of `x` to `out`. -/
@[inline] def pushU8 (out : ByteArray) (x : UInt8) : ByteArray := out.push x

/-- Append `x` as 2 little-endian bytes. -/
def pushU16LE (out : ByteArray) (x : UInt16) : ByteArray :=
  out
    |>.push x.toUInt8
    |>.push (x >>> 8).toUInt8

/-- Append `x` as 4 little-endian bytes. -/
def pushU32LE (out : ByteArray) (x : UInt32) : ByteArray :=
  out
    |>.push x.toUInt8
    |>.push (x >>> 8).toUInt8
    |>.push (x >>> 16).toUInt8
    |>.push (x >>> 24).toUInt8

/-- Append `x` as 8 little-endian bytes. -/
def pushU64LE (out : ByteArray) (x : UInt64) : ByteArray :=
  out
    |>.push x.toUInt8
    |>.push (x >>> 8).toUInt8
    |>.push (x >>> 16).toUInt8
    |>.push (x >>> 24).toUInt8
    |>.push (x >>> 32).toUInt8
    |>.push (x >>> 40).toUInt8
    |>.push (x >>> 48).toUInt8
    |>.push (x >>> 56).toUInt8

/-- Read 1 byte from `bs` at offset `off`. -/
@[inline] def readU8 (bs : ByteArray) (off : Nat) : UInt8 := bs.get! off

/-- Read 2 little-endian bytes from `bs` at offset `off` as `UInt16`. -/
def readU16LE (bs : ByteArray) (off : Nat) : UInt16 :=
  let b0 := (bs.get! off).toUInt16
  let b1 := (bs.get! (off + 1)).toUInt16
  b0 ||| (b1 <<< 8)

/-- Read 4 little-endian bytes from `bs` at offset `off` as `UInt32`. -/
def readU32LE (bs : ByteArray) (off : Nat) : UInt32 :=
  let b0 := (bs.get! off).toUInt32
  let b1 := (bs.get! (off + 1)).toUInt32
  let b2 := (bs.get! (off + 2)).toUInt32
  let b3 := (bs.get! (off + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Read 8 little-endian bytes from `bs` at offset `off` as `UInt64`. -/
def readU64LE (bs : ByteArray) (off : Nat) : UInt64 :=
  let b0 := (bs.get! off).toUInt64
  let b1 := (bs.get! (off + 1)).toUInt64
  let b2 := (bs.get! (off + 2)).toUInt64
  let b3 := (bs.get! (off + 3)).toUInt64
  let b4 := (bs.get! (off + 4)).toUInt64
  let b5 := (bs.get! (off + 5)).toUInt64
  let b6 := (bs.get! (off + 6)).toUInt64
  let b7 := (bs.get! (off + 7)).toUInt64
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)
    ||| (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)

end LeanSpec.Codec.Endian
