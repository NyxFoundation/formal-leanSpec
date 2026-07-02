/-
Casper-FFG checkpoints and the attestation vote they anchor.

Mirrors `src/lean_spec/spec/forks/lstar/containers/checkpoint.py` in leanSpec:
  - `class Checkpoint(Container)` — a (block root, slot) pair that can be
    justified and finalized, with `advance_to` enforcing forward-only
    progression.
  - `class AttestationData(Container)` — the three-checkpoint chain view
    (source, target, head) a validator attests to.

`AttestationData.lies_on_chain` is omitted until the fork-choice
propositions (FC-3) need it.

Supports CONT-1 and the ST-* propositions from
`docs/lean4-proof-propositions.md` (no theorems in this file).
-/

import LeanSpec.Aliases

namespace LeanSpec.Forks.Lstar

/-- A (block root, slot) pair that can be justified and finalized. -/
structure Checkpoint where
  root : Root
  slot : Slot
  deriving Inhabited, BEq, Repr

namespace Checkpoint

/-- The later of two checkpoints, keeping this one on a slot tie
(`Checkpoint.advance_to`). The candidate replaces this checkpoint only when
its slot is strictly higher, enforcing forward-only progression. -/
def advanceTo (self candidate : Checkpoint) : Checkpoint :=
  if candidate.slot > self.slot then candidate else self

end Checkpoint

/-- Attestation content describing the validator's observed chain view. -/
structure AttestationData where
  slot : Slot
  head : Checkpoint
  target : Checkpoint
  source : Checkpoint
  deriving Inhabited, BEq, Repr

end LeanSpec.Forks.Lstar
