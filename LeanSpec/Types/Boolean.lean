/-
  SSZ Boolean scalar.

  Mirrors `src/lean_spec/types/boolean.py`. Encoded as a single byte:
  `0x00` for `false`, `0x01` for `true`. Any other byte is rejected
  during deserialization.
-/

import LeanSpec.Types.Base

namespace LeanSpec.Types

/-- SSZ Boolean: a thin wrapper over Lean `Bool`. -/
structure Boolean where
  val : Bool
  deriving BEq, Repr, Inhabited

namespace Boolean

instance : SSZType Boolean where
  isFixedSize := true
  fixedByteLength := 1
  serialize x out := out.push (if x.val then 0x01 else 0x00)
  deserialize bs off sz :=
    if sz != 1 then
      .error (.sizeMismatch 1 sz)
    else if off + 1 > bs.size then
      .error (.underflow 1 (bs.size - off))
    else
      let b := bs.get! off
      if b = 0x00 then .ok ⟨false⟩
      else if b = 0x01 then .ok ⟨true⟩
      else .error (.invalidBoolean b)

end Boolean

end LeanSpec.Types
