/-
Casper-FFG checkpoints and the attestation vote they anchor.

Mirrors `src/lean_spec/spec/forks/lstar/containers/checkpoint.py` in leanSpec:
  - `class Checkpoint(Container)` — a (block root, slot) pair that can be
    justified and finalized, with `advance_to` enforcing forward-only
    progression.
  - `class AttestationData(Container)` — the three-checkpoint chain view
    (source, target, head) a validator attests to.

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

namespace AttestationData

/-- Check that every checkpoint (source, target, head) points to a block on
the given chain view (`lies_on_chain`): false when any root is the zero
hash or any checkpoint slot is past the end of the chain view; otherwise
all three roots must match the chain at their slot. -/
def liesOnChain (d : AttestationData) (historicalBlockHashes : Array Root) : Bool :=
  let zero := SSZ.Bytes32.zero
  if d.source.root == zero || d.target.root == zero || d.head.root == zero then
    false
  else
    let n := historicalBlockHashes.size
    let sourceSlot := d.source.slot.toNat
    let targetSlot := d.target.slot.toNat
    let headSlot := d.head.slot.toNat
    if n ≤ sourceSlot ∨ n ≤ targetSlot ∨ n ≤ headSlot then
      false
    else
      d.source.root == historicalBlockHashes[sourceSlot]! &&
      d.target.root == historicalBlockHashes[targetSlot]! &&
      d.head.root == historicalBlockHashes[headSlot]!

end AttestationData

end LeanSpec.Forks.Lstar
