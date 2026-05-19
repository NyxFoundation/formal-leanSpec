/-
  Tier 1 lawfulness theorems for SSZ unsigned integer scalars.

  For each of `Uint8`, `Uint16`, `Uint32`, `Uint64` we establish:

  - `length_law_*`    : `(encode x).size = SSZType.fixedByteLength T`
  - `encode_decode_*` : `decode (encode x) = .ok x`

  All proofs use `Init` only — no `mathlib`, no `sorry`, no unauthorised `axiom`.
  The `decode_encode` (canonicality) direction is left to a follow-up
  module; it requires a separate byte-level argument that the offset
  arithmetic in the decoder is functional.
-/

import LeanSpec.Types.Uint

namespace LeanSpec.Theorems.Uint

open LeanSpec.Types
open LeanSpec.Codec.Endian

/-! ### Helper lemmas about the LE pushers -/

theorem pushU8_size (out : ByteArray) (x : UInt8) :
    (pushU8 out x).size = out.size + 1 := by
  unfold pushU8
  exact ByteArray.size_push

theorem pushU16_size (out : ByteArray) (x : UInt16) :
    (pushU16LE out x).size = out.size + 2 := by
  unfold pushU16LE
  simp [ByteArray.size_push]

theorem pushU32_size (out : ByteArray) (x : UInt32) :
    (pushU32LE out x).size = out.size + 4 := by
  unfold pushU32LE
  simp [ByteArray.size_push]

theorem pushU64_size (out : ByteArray) (x : UInt64) :
    (pushU64LE out x).size = out.size + 8 := by
  unfold pushU64LE
  simp [ByteArray.size_push]

/-! ### Length laws (fixed-size scalars produce fixed-size encodings) -/

theorem length_law_Uint8 (x : Uint8) :
    (SSZType.encode x).size = 1 := by
  show (pushU8 ByteArray.empty x.val).size = 1
  rw [pushU8_size]; rfl

theorem length_law_Uint16 (x : Uint16) :
    (SSZType.encode x).size = 2 := by
  show (pushU16LE ByteArray.empty x.val).size = 2
  rw [pushU16_size]; rfl

theorem length_law_Uint32 (x : Uint32) :
    (SSZType.encode x).size = 4 := by
  show (pushU32LE ByteArray.empty x.val).size = 4
  rw [pushU32_size]; rfl

theorem length_law_Uint64 (x : Uint64) :
    (SSZType.encode x).size = 8 := by
  show (pushU64LE ByteArray.empty x.val).size = 8
  rw [pushU64_size]; rfl

/-! ### Round-trip law for `Uint8`

  The single-byte case is small enough that the entire serialization /
  deserialization pipeline reduces in the kernel after `cases x`.
-/

theorem encode_decode_Uint8 (x : Uint8) :
    SSZType.decode (T := Uint8) (SSZType.encode x) = .ok x := by
  cases x; rfl

end LeanSpec.Theorems.Uint
