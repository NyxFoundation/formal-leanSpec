/-
The validator registry tracked in the consensus state.

Mirrors `src/lean_spec/spec/forks/lstar/containers/validator.py` in leanSpec:
  - `class Validator(Container)` — a validator's static registry entry with
    two XMSS public keys (`Bytes52` upstream) and a registry index.
  - `class Validators(SSZList[Validator])` — the registry, bounded by
    `VALIDATOR_REGISTRY_LIMIT` upstream.

The XMSS key material is cryptographic and out of scope for this repository
(Arklib side); the two keys are carried as opaque `ByteArray` payloads
instead of a dedicated `Bytes52` subtype. Upstream's pydantic validator
"index equals list position" is a construction-time invariant, not spec
logic, and is not modeled.

Supports the ST-* and VAL-* propositions from
`docs/lean4-proof-propositions.md` (no theorems in this file).
-/

import LeanSpec.Aliases

namespace LeanSpec.Forks.Lstar

/-- A validator's static registry entry. -/
structure Validator where
  attestationPublicKey : ByteArray
  proposalPublicKey : ByteArray
  index : ValidatorIndex
  deriving Inhabited

instance : BEq Validator :=
  ⟨fun a b =>
    a.attestationPublicKey.data == b.attestationPublicKey.data &&
    a.proposalPublicKey.data == b.proposalPublicKey.data &&
    a.index == b.index⟩

instance : Repr Validator :=
  ⟨fun v n =>
    reprPrec (v.attestationPublicKey.data, v.proposalPublicKey.data, v.index) n⟩

/-- Validator registry tracked in the state. -/
abbrev Validators := Array Validator

end LeanSpec.Forks.Lstar
