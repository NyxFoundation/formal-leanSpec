/-
  `hashTreeRoot` dispatch.

  Mirrors `src/lean_spec/subspecs/ssz/hash.py`. The Python implementation
  uses `singledispatch` to switch on runtime type; Lean uses a type class
  `HasHashTreeRoot` whose instances are declared per-type module.
-/

import LeanSpec.Types.ByteArray

namespace LeanSpec.SSZ.Hash

open LeanSpec.Types

/-- Types that have a Merkle root. Each SSZ type module declares its own
    instance; primitive packings live alongside the type. -/
class HasHashTreeRoot (T : Type) where
  hashTreeRoot : T → Bytes32

/-- Convenience accessor mirroring the Python entry point. -/
@[inline] def hashTreeRoot {T : Type} [HasHashTreeRoot T] (x : T) : Bytes32 :=
  HasHashTreeRoot.hashTreeRoot x

end LeanSpec.SSZ.Hash
