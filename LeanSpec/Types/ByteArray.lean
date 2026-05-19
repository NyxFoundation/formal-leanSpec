/-
  SSZ byte-array types.

  Mirrors `src/lean_spec/types/byte_arrays.py`:
  - `BaseBytes` (fixed length, IS-A) → `BytesN n`
  - `BaseByteList` (variable, HAS-A, with `limit`) → `ByteList limit`

  Common specialisations are exposed as abbreviations: `Bytes32`, `Bytes20`,
  `Bytes65`, etc. Only the sizes used by the five in-scope containers are
  defined here; the rest can be added as `abbrev` lines without touching
  the encoding logic.

  Well-formedness (`data.size = n` for `BytesN n`, `data.size ≤ limit` for
  `ByteList limit`) is checked by `deserialize` and is the caller's
  responsibility for `serialize`. The structure wrapper does not statically
  enforce the size to keep proofs of round-trip lawfulness tractable in
  pure Lean.
-/

import LeanSpec.Types.Base

namespace LeanSpec.Types

/-- Fixed-length SSZ byte array of declared length `n`. -/
structure BytesN (n : Nat) where
  data : ByteArray
  deriving Inhabited

namespace BytesN

variable {n : Nat}

/-- Structural equality on the underlying `ByteArray` payload. -/
def beq (a b : BytesN n) : Bool := a.data = b.data

instance : BEq (BytesN n) := ⟨beq⟩

instance : SSZType (BytesN n) where
  isFixedSize := true
  fixedByteLength := n
  serialize x out := out ++ x.data
  deserialize bs off sz :=
    if sz != n then
      .error (.sizeMismatch n sz)
    else if off + n > bs.size then
      .error (.underflow n (bs.size - off))
    else
      .ok ⟨bs.extract off (off + n)⟩

end BytesN

/-- 20-byte fixed array (e.g. Ethereum-style address payload). -/
abbrev Bytes20 := BytesN 20

/-- 32-byte fixed array (Merkle root, hash digest). -/
abbrev Bytes32 := BytesN 32

/-- 48-byte fixed array (BLS public key shape; reserved for future). -/
abbrev Bytes48 := BytesN 48

/-- 96-byte fixed array (BLS signature shape; reserved for future). -/
abbrev Bytes96 := BytesN 96

/-- All-zero `Bytes32` constant used by the merkleisation zero-hash cache. -/
def zeroBytes32 : Bytes32 := ⟨ByteArray.mk (Array.replicate 32 (0 : UInt8))⟩

/-- Variable-length SSZ byte list bounded by `limit` bytes. -/
structure ByteList (limit : Nat) where
  data : ByteArray
  deriving Inhabited

namespace ByteList

variable {limit : Nat}

def beq (a b : ByteList limit) : Bool := a.data = b.data

instance : BEq (ByteList limit) := ⟨beq⟩

instance : SSZType (ByteList limit) where
  isFixedSize := false
  fixedByteLength := 0
  serialize x out := out ++ x.data
  deserialize bs off sz :=
    if sz > limit then
      .error (.tooManyElements limit sz)
    else if off + sz > bs.size then
      .error (.underflow sz (bs.size - off))
    else
      .ok ⟨bs.extract off (off + sz)⟩

end ByteList

end LeanSpec.Types
