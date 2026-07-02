/-
State-transition rejection errors.

Mirrors `src/lean_spec/spec/forks/lstar/errors.py` in leanSpec, where
`SpecRejectionError` carries a `RejectionReason`. The variants map to the
reasons raised by the state-transition function:
  - `slotNotInFuture`     ↔ `BLOCK_SLOT_NOT_IN_FUTURE`
  - `invalidSlot`         ↔ `BLOCK_SLOT_MISMATCH`
  - `headerSlotNotNewer`  ↔ `BLOCK_OLDER_THAN_LATEST_HEADER`
  - `proposerMismatch`    ↔ `WRONG_PROPOSER`
  - `parentRootMismatch`  ↔ `PARENT_ROOT_MISMATCH`

Python models failure by raising; Lean models it with `Except`, following
the catalog samples (`State.processBlockHeader s b = .ok s'`).

`proposerMismatch` and `parentRootMismatch` are pre-declared for the
follow-up that widens the `process_block_header` validation surface
(they need `validators` and `hash_tree_root` respectively).

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
  | parentRootMismatch (expected actual : Root) : STError
  | proposerMismatch (expected actual : ValidatorIndex) : STError
  deriving Repr, BEq, Inhabited

/-- Result of a fallible state-transition step. -/
abbrev ST.Result := Except STError

end LeanSpec.Forks.Lstar
