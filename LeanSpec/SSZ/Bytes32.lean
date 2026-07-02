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

/-- The all-zero 32-byte value (`Bytes32.zero()` in leanSpec, aka `ZERO_HASH`). -/
def zero : Bytes32 := ⟨⟨Array.replicate 32 0⟩, by simp [ByteArray.size]⟩

instance : Inhabited Bytes32 := ⟨zero⟩

instance : BEq Bytes32 := ⟨fun a b => a.val.data == b.val.data⟩

instance : Repr Bytes32 := ⟨fun b n => reprPrec b.val.data n⟩

end Bytes32
end LeanSpec.SSZ
