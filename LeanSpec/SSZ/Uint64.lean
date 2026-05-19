/-
SSZ Uint64 primitive.

Mirrors `src/lean_spec/types/uint.py` in leanSpec:
  - `class Uint64(BaseUint)` with `BITS = 64`
  - `__new__` enforces `0 <= value <= 2^64 - 1`

In Lean we reuse the core `UInt64` type, whose internal representation
`Fin UInt64.size` (with `UInt64.size = 2 ^ 64`) coincides with the
Python-side range invariant.

Proves SSZ-2 from `docs/lean4-proof-propositions.md`:
  `∀ v : Uint64, v.toNat < 2 ^ 64`.
-/

namespace LeanSpec.SSZ

abbrev Uint64 := UInt64

namespace Uint64

theorem range (v : Uint64) : v.toNat < 2 ^ 64 :=
  v.toNat_lt

end Uint64
end LeanSpec.SSZ
