/-
  BlockHeader container.

  Mirrors `src/lean_spec/subspecs/containers/block/block.py`.
  Fixed-size: slot (8) + proposerIndex (8) + parentRoot (32) + stateRoot (32) + bodyRoot (32) = 112 bytes.
-/

import LeanSpec.Aliases
import LeanSpec.Types.Base

namespace LeanSpec.Containers

open LeanSpec
open LeanSpec.Types

/-- Metadata summarising a block: parent reference, state root, body root. -/
structure BlockHeader where
  slot          : Slot
  proposerIndex : ValidatorIndex
  parentRoot    : Root
  stateRoot     : Root
  bodyRoot      : Root
  deriving BEq, Inhabited

namespace BlockHeader

def byteLength : Nat := 8 + 8 + 32 + 32 + 32

instance : SSZType BlockHeader where
  isFixedSize := true
  fixedByteLength := byteLength
  serialize x out :=
    SSZType.serialize x.bodyRoot
      (SSZType.serialize x.stateRoot
        (SSZType.serialize x.parentRoot
          (SSZType.serialize x.proposerIndex
            (SSZType.serialize x.slot out))))
  deserialize bs off sz :=
    if sz ≠ byteLength then
      .error (.sizeMismatch byteLength sz)
    else if off + sz > bs.size then
      .error (.underflow sz (bs.size - off))
    else
      match SSZType.deserialize (T := Slot) bs off 8 with
      | .error e => .error e
      | .ok slot =>
        match SSZType.deserialize (T := ValidatorIndex) bs (off + 8) 8 with
        | .error e => .error e
        | .ok proposerIndex =>
          match SSZType.deserialize (T := Root) bs (off + 16) 32 with
          | .error e => .error e
          | .ok parentRoot =>
            match SSZType.deserialize (T := Root) bs (off + 48) 32 with
            | .error e => .error e
            | .ok stateRoot =>
              match SSZType.deserialize (T := Root) bs (off + 80) 32 with
              | .error e => .error e
              | .ok bodyRoot => .ok ⟨slot, proposerIndex, parentRoot, stateRoot, bodyRoot⟩

end BlockHeader
end LeanSpec.Containers
