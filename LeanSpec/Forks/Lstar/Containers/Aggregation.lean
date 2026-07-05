/-
Signature-aggregation containers.

Mirrors `src/lean_spec/spec/forks/lstar/containers/aggregation.py` in
leanSpec:
  - `class SingleMessageAggregate(Container)` — single-message proof
    aggregating signatures from many validators; `participants` names the
    signers, `proof` carries the aggregated signature material.

The `aggregate` construction and proof verification are XMSS material and
out of scope for this repository (Arklib side); as with
`MultiMessageAggregate` (`Containers/Block.lean`), only the serialized
proof payload is carried, opaquely. Fork choice reads nothing from an
aggregate but its `participants`.

Supports the FC-* propositions from `docs/lean4-proof-propositions.md`
(no theorems in this file).
-/

import LeanSpec.Forks.Lstar.Containers.Attestation

namespace LeanSpec.Forks.Lstar

/-- Single-message proof aggregating signatures from many validators
(`SingleMessageAggregate`): every named validator signed the same message
for the same slot; message and slot stay outside the proof. The proof
bytes are opaque XMSS material (`ByteList512KiB` upstream). -/
structure SingleMessageAggregate where
  participants : AggregationBits
  proof : ByteArray
  deriving Inhabited

end LeanSpec.Forks.Lstar
