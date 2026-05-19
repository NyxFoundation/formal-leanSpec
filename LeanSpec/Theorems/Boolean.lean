/-
  Tier 1 lawfulness theorems for the SSZ Boolean scalar.

  - `length_law`     : `(encode x).size = 1`
  - `encode_decode`  : `decode (encode x) = .ok x`

  Both proofs go through by case analysis on the underlying `Bool` —
  small enough that the entire pipeline reduces in the kernel.
-/

import LeanSpec.Types.Boolean

namespace LeanSpec.Theorems.Boolean

open LeanSpec.Types

theorem length_law (x : Boolean) :
    (SSZType.encode x).size = 1 := by
  cases x with
  | mk b => cases b <;> rfl

theorem encode_decode (x : Boolean) :
    SSZType.decode (T := Boolean) (SSZType.encode x) = .ok x := by
  cases x with
  | mk b => cases b <;> rfl

end LeanSpec.Theorems.Boolean
