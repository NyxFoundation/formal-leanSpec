/-
Attestation vote envelopes.

Mirrors `src/lean_spec/spec/forks/lstar/containers/attestation.py` and
`containers/participation.py` in leanSpec:
  - `AggregationBits` — bitfield naming the validators in an aggregate
    (an SSZ bitlist; modeled as `Array Bool`).
  - `class Attestation(Container)` — a validator-specific attestation
    wrapping shared attestation data.
  - `class AggregatedAttestation(Container)` — attestation shared by many
    validators, with a bitfield naming them.

The signed variants (`SignedAttestation`, `SignedAggregatedAttestation`)
carry XMSS signature material and are omitted — signature schemes are out
of scope for this repository (Arklib side).

Supports the ST-* propositions from `docs/lean4-proof-propositions.md`
(no theorems in this file).
-/

import LeanSpec.Forks.Lstar.Containers.Checkpoint

namespace LeanSpec.Forks.Lstar

/-- Bitfield indicating which validators participated in an aggregation
(SSZ bitlist bounded by `VALIDATOR_REGISTRY_LIMIT` upstream). -/
abbrev AggregationBits := Array Bool

/-- Validator-specific attestation wrapping shared attestation data. -/
structure Attestation where
  validatorIndex : ValidatorIndex
  data : AttestationData
  deriving Inhabited, BEq, Repr

/-- Attestation shared by many validators, with a bitfield naming them. -/
structure AggregatedAttestation where
  aggregationBits : AggregationBits
  data : AttestationData
  deriving Inhabited, BEq, Repr

end LeanSpec.Forks.Lstar
