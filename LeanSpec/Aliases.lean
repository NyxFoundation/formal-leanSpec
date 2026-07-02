/-
Scalar aliases shared across the consensus layer.

Mirrors in leanSpec:
  - `src/lean_spec/spec/forks/lstar/slot.py`:
      `class Slot(Uint64)` — a slot number, as a 64-bit unsigned integer.
  - `src/lean_spec/spec/forks/lstar/containers/identifiers.py`:
      `class ValidatorIndex(Uint64)` — a validator's registry index.
  - `Bytes32` roots from `src/lean_spec/spec/ssz`.

`Slot` and `ValidatorIndex` are Python subclasses of `Uint64`; in Lean they
are abbreviations of `Uint64` (= core `UInt64`), inheriting all arithmetic,
order, and decidability structure from core. Behavior specific to these
types (`is_justifiable_after`, `proposer_for_slot`, …) is added where the
propositions that consume it live (CONT-2, VAL-1).
-/

import LeanSpec.SSZ.Uint64
import LeanSpec.SSZ.Bytes32

namespace LeanSpec

/-- A slot number (`class Slot(Uint64)`). -/
abbrev Slot := SSZ.Uint64

/-- A validator's index in the registry (`class ValidatorIndex(Uint64)`). -/
abbrev ValidatorIndex := SSZ.Uint64

/-- A 32-byte root hash. -/
abbrev Root := SSZ.Bytes32

end LeanSpec
