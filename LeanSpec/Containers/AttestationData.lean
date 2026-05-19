/-
  AttestationData container.

  Mirrors `src/lean_spec/subspecs/containers/attestation/attestation.py`.
  Fixed-size: slot (8) + head (40) + target (40) + source (40) = 128 bytes.
-/

import LeanSpec.Containers.Checkpoint

namespace LeanSpec.Containers

open LeanSpec
open LeanSpec.Types

/-- Validator's observed chain view at a given slot. -/
structure AttestationData where
  slot   : Slot
  head   : Checkpoint
  target : Checkpoint
  source : Checkpoint
  deriving BEq, Inhabited

namespace AttestationData

def byteLength : Nat := 8 + Checkpoint.byteLength * 3

instance : SSZType AttestationData where
  isFixedSize := true
  fixedByteLength := byteLength
  serialize x out :=
    SSZType.serialize x.source
      (SSZType.serialize x.target
        (SSZType.serialize x.head
          (SSZType.serialize x.slot out)))
  deserialize bs off sz :=
    let cp := Checkpoint.byteLength
    if sz ≠ byteLength then
      .error (.sizeMismatch byteLength sz)
    else if off + sz > bs.size then
      .error (.underflow sz (bs.size - off))
    else
      match SSZType.deserialize (T := Slot) bs off 8 with
      | .error e => .error e
      | .ok slot =>
        match SSZType.deserialize (T := Checkpoint) bs (off + 8) cp with
        | .error e => .error e
        | .ok head =>
          match SSZType.deserialize (T := Checkpoint) bs (off + 8 + cp) cp with
          | .error e => .error e
          | .ok target =>
            match SSZType.deserialize (T := Checkpoint) bs (off + 8 + cp * 2) cp with
            | .error e => .error e
            | .ok source => .ok ⟨slot, head, target, source⟩

end AttestationData
end LeanSpec.Containers
