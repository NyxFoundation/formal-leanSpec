/-
  Unsigned integer SSZ scalars.

  Mirrors `src/lean_spec/types/uint.py` (`BaseUint`), restricted to
  `Uint8/16/32/64`. Each type wraps the corresponding native Lean
  `UIntN` so the well-formedness `val < 2^N` is automatic.

  `Uint256` is intentionally not exposed as a first-class type in this
  phase; the only place leanSpec needs a 32-byte little-endian integer
  is inside `mixInLength` / `mixInSelector`, which build it directly
  from a `Nat`.
-/

import LeanSpec.Types.Base
import LeanSpec.Codec.Endian

namespace LeanSpec.Types

open LeanSpec.Codec.Endian

/-- 8-bit unsigned SSZ integer. -/
structure Uint8 where
  val : UInt8
  deriving BEq, Repr, Inhabited

/-- 16-bit unsigned SSZ integer. -/
structure Uint16 where
  val : UInt16
  deriving BEq, Repr, Inhabited

/-- 32-bit unsigned SSZ integer. -/
structure Uint32 where
  val : UInt32
  deriving BEq, Repr, Inhabited

/-- 64-bit unsigned SSZ integer. -/
structure Uint64 where
  val : UInt64
  deriving BEq, Repr, Inhabited

namespace Uint8

instance : SSZType Uint8 where
  isFixedSize := true
  fixedByteLength := 1
  serialize x out := pushU8 out x.val
  deserialize bs off sz :=
    if sz != 1 then
      .error (.sizeMismatch 1 sz)
    else if off + 1 > bs.size then
      .error (.underflow 1 (bs.size - off))
    else
      .ok ⟨readU8 bs off⟩

end Uint8

namespace Uint16

instance : SSZType Uint16 where
  isFixedSize := true
  fixedByteLength := 2
  serialize x out := pushU16LE out x.val
  deserialize bs off sz :=
    if sz != 2 then
      .error (.sizeMismatch 2 sz)
    else if off + 2 > bs.size then
      .error (.underflow 2 (bs.size - off))
    else
      .ok ⟨readU16LE bs off⟩

end Uint16

namespace Uint32

instance : SSZType Uint32 where
  isFixedSize := true
  fixedByteLength := 4
  serialize x out := pushU32LE out x.val
  deserialize bs off sz :=
    if sz != 4 then
      .error (.sizeMismatch 4 sz)
    else if off + 4 > bs.size then
      .error (.underflow 4 (bs.size - off))
    else
      .ok ⟨readU32LE bs off⟩

end Uint32

namespace Uint64

instance : SSZType Uint64 where
  isFixedSize := true
  fixedByteLength := 8
  serialize x out := pushU64LE out x.val
  deserialize bs off sz :=
    if sz != 8 then
      .error (.sizeMismatch 8 sz)
    else if off + 8 > bs.size then
      .error (.underflow 8 (bs.size - off))
    else
      .ok ⟨readU64LE bs off⟩

end Uint64

end LeanSpec.Types
