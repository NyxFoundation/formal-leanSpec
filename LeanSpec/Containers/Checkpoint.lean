/-
  Checkpoint container.

  Mirrors `src/lean_spec/subspecs/containers/checkpoint.py`. Fixed-size:
  `root` (32 bytes) followed by `slot` (8 bytes) → 40 bytes total.
-/

import LeanSpec.Aliases
import LeanSpec.Types.Base

namespace LeanSpec.Containers

open LeanSpec
open LeanSpec.Types

/-- A reference into the chain's history: a block root paired with its slot. -/
structure Checkpoint where
  root : Root
  slot : Slot
  deriving BEq, Inhabited

namespace Checkpoint

/-- Total serialized size of every Checkpoint. -/
def byteLength : Nat := 32 + 8

instance : SSZType Checkpoint where
  isFixedSize := true
  fixedByteLength := byteLength
  serialize x out :=
    SSZType.serialize x.slot (SSZType.serialize x.root out)
  deserialize bs off sz :=
    if sz ≠ byteLength then
      .error (.sizeMismatch byteLength sz)
    else if off + sz > bs.size then
      .error (.underflow sz (bs.size - off))
    else
      match SSZType.deserialize (T := Root) bs off 32 with
      | .error e => .error e
      | .ok root =>
        match SSZType.deserialize (T := Slot) bs (off + 32) 8 with
        | .error e => .error e
        | .ok slot => .ok ⟨root, slot⟩

end Checkpoint
end LeanSpec.Containers
