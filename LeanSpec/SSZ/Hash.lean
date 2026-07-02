/-
SSZ hash_tree_root collision-resistance assumption.

Mirrors `src/lean_spec/spec/crypto/merkleization.py` in leanSpec:
  - `hash_tree_root(value) -> Bytes32` — a `@singledispatch` function whose
    per-type registered handlers compute the SSZ Merkle root of a value.

In Lean the per-type dispatch is modeled as the `HasHashTreeRoot` typeclass.
The underlying hash (SHA-256 Merkleization) is a cryptographic primitive and
out of scope for this repository — primitives live on the Arklib side per the
catalog's "Out of scope" notice — so its collision resistance is recorded as
an `axiom`, not proved.

Discharges SSZ-7 from `docs/lean4-proof-propositions.md`:
  - SSZ-7 [axiom]: distinct values produce distinct hash-tree roots
    (collision resistance).
-/

import LeanSpec.SSZ.Bytes32

namespace LeanSpec.SSZ

/-- Types carrying an SSZ Merkleization to a 32-byte root (models the
per-type `hash_tree_root.register` handlers of the Python spec). -/
class HasHashTreeRoot (T : Type) where
  hashTreeRoot : T → Bytes32

export HasHashTreeRoot (hashTreeRoot)

namespace HashTreeRoot

/--
SSZ-7: distinct values produce distinct hash-tree roots.

Not a strict theorem — a cryptographic assumption (idealized injectivity of
the SHA-256 Merkleization) consumed at call sites. It is meaningful only for
instances that model the real hash; `HasHashTreeRoot` must not be
instantiated with degenerate (non-injective) functions, or this axiom
becomes inconsistent.
-/
axiom collisionResistance {T : Type} [HasHashTreeRoot T] :
    ∀ x y : T, hashTreeRoot x = hashTreeRoot y → x = y

end HashTreeRoot
end LeanSpec.SSZ
