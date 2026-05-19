/-
  SSZType: minimal interface every SSZ-typed value implements.

  Mirrors `src/lean_spec/types/ssz_base.py:13` (`SSZType` ABC) but adapts the
  Pythonic stream-based API to a pure functional style based on `ByteArray`
  slicing. The streaming abstraction is unnecessary in Lean; offset/size
  arithmetic is explicit, which is also more amenable to inductive proofs.

  Design notes:

  - `serialize` is a builder: it appends bytes to an accumulator. This makes
    container encoding (which prepends an offset table built up incrementally)
    straightforward to write and reason about.

  - `deserialize` takes a byte array, a start offset, and a scope (length of
    the sub-slice the value occupies). This matches Python's
    `deserialize(stream, scope)` while remaining purely functional.

  - The `SSZError` type enumerates the failure modes the spec ascribes to
    decoding. Each constructor carries enough information for a useful error
    message but nothing transient.
-/

namespace LeanSpec.Types

/-- Failure modes when decoding an SSZ-encoded byte string. -/
inductive SSZError where
  /-- Total scope did not match the expected fixed-size byte length. -/
  | sizeMismatch (expected actual : Nat) : SSZError
  /-- An offset pointed outside the enclosing scope. -/
  | offsetOutOfRange (offset scope : Nat) : SSZError
  /-- Offsets in a variable-length container or list were not monotone. -/
  | offsetNotMonotone : SSZError
  /-- First offset in a variable-length container did not equal `numFields * 4`. -/
  | offsetTableMisaligned (firstOffset expected : Nat) : SSZError
  /-- Bitlist did not have a sentinel `1` bit at or after the highest data bit. -/
  | invalidBitlistSentinel : SSZError
  /-- Bitvector tail had non-zero high bits beyond the declared length. -/
  | invalidBitvectorTail : SSZError
  /-- A boolean byte was neither `0x00` nor `0x01`. -/
  | invalidBoolean (byte : UInt8) : SSZError
  /-- Decoded element count exceeded the declared limit/length. -/
  | tooManyElements (limit count : Nat) : SSZError
  /-- The supplied byte slice was shorter than required to read the next field. -/
  | underflow (needed available : Nat) : SSZError
  /-- A free-form constraint failed; carries a short diagnostic message. -/
  | malformed (msg : String) : SSZError
  deriving Repr, BEq, Inhabited

/-- Convenience alias for SSZ decoding results. -/
abbrev SSZ.Result := Except SSZError

/-- Common interface for every SSZ-encoded type. -/
class SSZType (T : Type) where
  /-- True iff every value of `T` serializes to the same number of bytes. -/
  isFixedSize : Bool
  /--
    Byte length of every value of `T` when `isFixedSize = true`.

    For variable-size types this is treated as a lower bound (the size of the
    fixed-size header that must always be present, e.g. `4` for an empty
    `SSZList` of variable elements). Callers may not assume it is the exact
    serialized length when `isFixedSize = false`.
  -/
  fixedByteLength : Nat
  /-- Append the SSZ encoding of `x` to `out`. -/
  serialize : T → (out : ByteArray) → ByteArray
  /-- Read a `T` from `bs[off : off + sz]`. -/
  deserialize : (bs : ByteArray) → (off sz : Nat) → SSZ.Result T

namespace SSZType

variable {T : Type} [SSZType T]

/-- Top-level encoder: serialize `x` to a fresh `ByteArray`. -/
def encode (x : T) : ByteArray := serialize x ByteArray.empty

/-- Top-level decoder: read a `T` from the entire `bs`. -/
def decode (bs : ByteArray) : SSZ.Result T :=
  deserialize bs 0 bs.size

end SSZType
end LeanSpec.Types
