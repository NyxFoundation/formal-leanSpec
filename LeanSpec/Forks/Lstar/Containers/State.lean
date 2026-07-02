/-
Consensus state and the justification/finalization accounting it tracks.

Mirrors `src/lean_spec/spec/forks/lstar/containers/state.py` in leanSpec:
  - `HistoricalBlockHashes`, `JustificationRoots` — `SSZList[Bytes32]`.
  - `JustifiedSlots` — bitlist tracking justified slots relative to the
    finalized boundary, with `is_slot_justified` / `extend_to_slot`.
  - `JustificationValidators` — per-root validator vote bitfields,
    concatenated into one flat bitlist.
  - `class State(Container)` — the main consensus state object.

SSZ lists/bitlists are modeled as `Array`; the upstream `LIMIT` bounds are
not enforced by the model (see `Config.lean`). Upstream
`is_slot_justified` raises `JUSTIFIED_SLOT_OUT_OF_RANGE` for an active slot
outside the tracked range; here it returns `ST.Result Bool`.

Supports the ST-* propositions from `docs/lean4-proof-propositions.md`
(no theorems in this file).
-/

import LeanSpec.Forks.Lstar.Containers.Block
import LeanSpec.Forks.Lstar.Containers.Genesis
import LeanSpec.Forks.Lstar.Containers.Validator
import LeanSpec.Forks.Lstar.Errors
import LeanSpec.Forks.Lstar.Slot

namespace LeanSpec.Forks.Lstar

/-- List of historical block root hashes. -/
abbrev HistoricalBlockHashes := Array Root

/-- Roots of blocks with pending justification tallies. -/
abbrev JustificationRoots := Array Root

/-- Bitlist tracking justified slots relative to the finalized boundary. -/
abbrev JustifiedSlots := Array Bool

/-- Per-root validator vote bitfields, concatenated into one flat bitlist. -/
abbrev JustificationValidators := Array Bool

namespace JustifiedSlots

/-- Whether `target` is considered justified (`is_slot_justified`): slots at
or before the finalized boundary are implicitly justified; later slots are
checked against the tracked bitfield, rejecting with
`JUSTIFIED_SLOT_OUT_OF_RANGE` when outside the tracked range. -/
def isSlotJustified (js : JustifiedSlots) (finalized target : Slot) :
    ST.Result Bool :=
  match Slot.justifiedIndexAfter finalized target with
  | none => .ok true
  | some i =>
    if h : i < js.size then .ok js[i]
    else .error (.justifiedSlotOutOfRange finalized target)

/-- Extend the tracking capacity to cover `target` (`extend_to_slot`),
filling the gap with `false`. -/
def extendToSlot (js : JustifiedSlots) (finalized target : Slot) :
    JustifiedSlots :=
  match Slot.justifiedIndexAfter finalized target with
  | none => js
  | some i =>
    if i + 1 ≤ js.size then js
    else js ++ Array.replicate (i + 1 - js.size) false

end JustifiedSlots

/-- The main consensus state object. -/
structure State where
  config : GenesisConfig
  slot : Slot
  latestBlockHeader : BlockHeader
  latestJustified : Checkpoint
  latestFinalized : Checkpoint
  historicalBlockHashes : HistoricalBlockHashes
  justifiedSlots : JustifiedSlots
  validators : Validators
  justificationsRoots : JustificationRoots
  justificationsValidators : JustificationValidators
  deriving Inhabited, BEq, Repr

end LeanSpec.Forks.Lstar
