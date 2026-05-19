/-
  Generic helpers used by SSZ merkleisation and offset arithmetic.
  Mirrors `src/lean_spec/subspecs/ssz/utils.py`.
-/

import LeanSpec.Crypto.Sha256
import LeanSpec.Types.ByteArray

namespace LeanSpec.SSZ.Utils

open LeanSpec.Crypto.Sha256
open LeanSpec.Types

/-- Smallest power of two `≥ x`. Returns `1` for `x ≤ 1`. -/
def getPowerOfTwoCeil (x : Nat) : Nat :=
  if x ≤ 1 then 1
  else
    let rec go (acc : Nat) (n : Nat) : Nat :=
      if acc ≥ x then acc
      else
        match n with
        | 0 => acc
        | n + 1 => go (acc * 2) n
    go 1 64

/-- Hash two 32-byte chunks together via SHA-256. -/
def hashNodes (a b : Bytes32) : Bytes32 :=
  ⟨sha256 (a.data ++ b.data)⟩

end LeanSpec.SSZ.Utils
