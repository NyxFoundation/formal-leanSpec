/-
Chain and consensus configuration constants.

Mirrors `src/lean_spec/spec/forks/lstar/config.py` in leanSpec. Only the
constants consumed by the ported state-transition logic are declared;
SSZ list limits (`HISTORICAL_ROOTS_LIMIT`, `VALIDATOR_REGISTRY_LIMIT`, …)
are not enforced by the Lean `Array` model and are added when a
proposition needs them.

Supports the ST-* propositions from `docs/lean4-proof-propositions.md`
(no theorems in this file).
-/

namespace LeanSpec.Forks.Lstar

/-- Maximum number of distinct attestation data entries per block
(`MAX_ATTESTATIONS_DATA`, a `Uint8` upstream). -/
def MAX_ATTESTATIONS_DATA : Nat := 8

end LeanSpec.Forks.Lstar
