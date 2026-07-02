/-
Block container family.

Mirrors `src/lean_spec/spec/forks/lstar/containers/block.py` in leanSpec:
  - `class BlockBody(Container)` — payload carrying attestations.
  - `class BlockHeader(Container)` — metadata summarizing a block without
    its body.
  - `class Block(Container)` — a complete block including header fields and
    body.
  - `class SignedBlock(Container)` — envelope carrying a block with a single
    aggregated proof for all signatures.

The `MultiMessageAggregate` proof type lives upstream in
`containers/aggregation.py` and is XMSS aggregation material — out of scope
for this repository (Arklib side) — so only its presence is modeled, as an
opaque byte payload.

Supports ST-2 / ST-3 / ST-5 / ST-6 from `docs/lean4-proof-propositions.md`
(no theorems in this file).
-/

import LeanSpec.Forks.Lstar.Containers.Attestation

namespace LeanSpec.Forks.Lstar

/-- Payload of a block containing attestations
(`AggregatedAttestations`, an SSZ list bounded by
`VALIDATOR_REGISTRY_LIMIT` upstream). -/
structure BlockBody where
  attestations : Array AggregatedAttestation
  deriving Inhabited, BEq, Repr

/-- Metadata summarizing a block without its body. -/
structure BlockHeader where
  slot : Slot
  proposerIndex : ValidatorIndex
  parentRoot : Root
  stateRoot : Root
  bodyRoot : Root
  deriving Inhabited, BEq, Repr

/-- A complete block including header fields and body. -/
structure Block where
  slot : Slot
  proposerIndex : ValidatorIndex
  parentRoot : Root
  stateRoot : Root
  body : BlockBody
  deriving Inhabited, BEq, Repr

/-- Opaque stand-in for the XMSS `MultiMessageAggregate` full-block proof
(`containers/aggregation.py` upstream). Internal structure and verification
are cryptographic and delegated to Arklib; only the serialized payload is
carried here. -/
structure MultiMessageAggregate where
  payload : ByteArray
  deriving Inhabited

/-- Envelope carrying a block with a single aggregated proof binding every
attestation in the body and the proposer signature over the block root. -/
structure SignedBlock where
  block : Block
  proof : MultiMessageAggregate
  deriving Inhabited

end LeanSpec.Forks.Lstar
