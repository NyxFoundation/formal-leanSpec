/-
State-transition rejection errors.

Mirrors `src/lean_spec/spec/forks/lstar/errors.py` in leanSpec, where
`SpecRejectionError` carries a `RejectionReason`. The variants map to the
reasons raised by the state-transition function:
  - `slotNotInFuture`           ↔ `BLOCK_SLOT_NOT_IN_FUTURE`
  - `invalidSlot`               ↔ `BLOCK_SLOT_MISMATCH`
  - `headerSlotNotNewer`        ↔ `BLOCK_OLDER_THAN_LATEST_HEADER`
  - `emptyValidatorRegistry`    ↔ `EMPTY_VALIDATOR_REGISTRY`
  - `proposerMismatch`          ↔ `WRONG_PROPOSER`
  - `parentRootMismatch`        ↔ `PARENT_ROOT_MISMATCH`
  - `tooManyAttestationData`    ↔ `TOO_MANY_ATTESTATION_DATA`
  - `emptyAggregationBits`      ↔ `EMPTY_AGGREGATION_BITS`
  - `validatorIndexOutOfRange`  ↔ `VALIDATOR_INDEX_OUT_OF_RANGE`
  - `justifiedSlotOutOfRange`   ↔ `JUSTIFIED_SLOT_OUT_OF_RANGE`

Python models failure by raising; Lean models it with `Except`, following
the catalog samples (`State.processBlockHeader s b = .ok s'`).

`parentRootMismatch` is pre-declared for the follow-up that widens the
`process_block_header` validation surface (it needs `hash_tree_root`).

Supports the ST-* propositions from `docs/lean4-proof-propositions.md`
(no theorems in this file).
-/

import LeanSpec.Aliases

namespace LeanSpec.Forks.Lstar

/-- Reasons the state-transition function rejects a block. -/
inductive STError where
  | slotNotInFuture (current target : Slot) : STError
  | invalidSlot (expected actual : Slot) : STError
  | headerSlotNotNewer : STError
  | emptyValidatorRegistry : STError
  | parentRootMismatch (expected actual : Root) : STError
  | proposerMismatch (expected actual : ValidatorIndex) : STError
  | tooManyAttestationData (count max : Nat) : STError
  | emptyAggregationBits : STError
  | validatorIndexOutOfRange : STError
  | justifiedSlotOutOfRange (finalized target : Slot) : STError
  deriving Repr, BEq, Inhabited

/-- Result of a fallible state-transition step. -/
abbrev ST.Result := Except STError

end LeanSpec.Forks.Lstar
