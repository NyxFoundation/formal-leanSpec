/-
SSZ Bytes32 primitive.

Mirrors `src/lean_spec/types/bytes.py` in leanSpec:
  - `Bytes32` is a fixed-length 32-byte sequence (subclass of Python `bytes`)
  - Length is statically guaranteed: every value has `len(b) == 32`

In Lean we model this as a `ByteArray` subtype carrying the size invariant.

Proves SSZ-4 from `docs/lean4-proof-propositions.md`:
  `∀ bs : Bytes32, bs.size = 32`.
-/

namespace LeanSpec.SSZ

abbrev Bytes32 := { bs : ByteArray // bs.size = 32 }

namespace Bytes32

@[inline] def size (b : Bytes32) : Nat := b.val.size

theorem size_eq_32 (b : Bytes32) : b.size = 32 := b.property

end Bytes32
end LeanSpec.SSZ
