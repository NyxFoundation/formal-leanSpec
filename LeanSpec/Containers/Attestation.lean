/-
  Attestation container.

  Mirrors `src/lean_spec/subspecs/containers/attestation/attestation.py`.
  Fixed-size: validatorId (8) + data (128) = 136 bytes.
-/

import LeanSpec.Containers.AttestationData

namespace LeanSpec.Containers

open LeanSpec
open LeanSpec.Types

/-- A single validator's signed attestation payload (without the signature). -/
structure Attestation where
  validatorId : ValidatorIndex
  data        : AttestationData
  deriving BEq, Inhabited

namespace Attestation

def byteLength : Nat := 8 + AttestationData.byteLength

instance : SSZType Attestation where
  isFixedSize := true
  fixedByteLength := byteLength
  serialize x out :=
    SSZType.serialize x.data (SSZType.serialize x.validatorId out)
  deserialize bs off sz :=
    if sz ≠ byteLength then
      .error (.sizeMismatch byteLength sz)
    else if off + sz > bs.size then
      .error (.underflow sz (bs.size - off))
    else
      match SSZType.deserialize (T := ValidatorIndex) bs off 8 with
      | .error e => .error e
      | .ok validatorId =>
        match SSZType.deserialize (T := AttestationData) bs (off + 8) AttestationData.byteLength with
        | .error e => .error e
        | .ok data => .ok ⟨validatorId, data⟩

end Attestation
end LeanSpec.Containers
