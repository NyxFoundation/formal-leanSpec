/-
  Consensus-layer type aliases used by the in-scope containers.

  Mirrors the lightweight subclasses in `src/lean_spec/subspecs/containers/`:

  - `Slot`            ≡ `Uint64`
  - `ValidatorIndex`  ≡ `Uint64`
  - `Root`            ≡ `Bytes32`
  - `AggregationBits` ≡ `Bitlist VALIDATOR_REGISTRY_LIMIT`

  Aliasing keeps the SSZType instance for the underlying primitive without
  introducing wrapper structs. The `VALIDATOR_REGISTRY_LIMIT` constant is
  the same `2^12 = 4096` used by `lean_spec.subspecs.chain.config`.
-/

import LeanSpec.Types.Uint
import LeanSpec.Types.ByteArray
import LeanSpec.Types.Bitfield

namespace LeanSpec

open LeanSpec.Types

/-- Validator registry limit per `lean_spec.subspecs.chain.config`. -/
def VALIDATOR_REGISTRY_LIMIT : Nat := 4096

/-- Slot number (Uint64). -/
abbrev Slot := Uint64

/-- Validator index (Uint64). -/
abbrev ValidatorIndex := Uint64

/-- Merkle/block root (Bytes32). -/
abbrev Root := Bytes32

/-- Aggregation bits bitlist bounded by the validator registry limit. -/
abbrev AggregationBits := Bitlist VALIDATOR_REGISTRY_LIMIT

end LeanSpec
