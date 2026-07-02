/-
State transition function.

Mirrors `src/lean_spec/spec/forks/lstar/state_transition.py` in leanSpec:
  - `generate_genesis(genesis_time, validators)`: the initial state.
  - `process_slots(state, target_slot)`: while `state.slot < target_slot`,
    advance `state.slot` by one.
  - `process_block_header(state, block)`: validate the header checks,
    anchor genesis checkpoints on the first block, record history, and
    install the block as `latest_block_header`.
  - `process_attestations(state, attestations)`: 3SF-mini justification
    and finalization — tally votes per target root, advance the justified
    checkpoint on a 2/3 supermajority, finalize the source when no
    justifiable slot sits between it and the target.
  - `process_block` / `state_transition`: composition.

Divergences from Python, documented per function:
  - `process_slots` upstream raises `BLOCK_SLOT_NOT_IN_FUTURE` when
    `target_slot ≤ state.slot`; in Lean `processSlots` is total (it returns
    the state unchanged) and that guard lives in `State.transition`,
    matching where `state_transition` consumes it.
  - All `hash_tree_root` computations are omitted (Merkleization is
    Arklib-side; SSZ-7 models only its injectivity): the pre-block
    state-root caching in `process_slots`, the
    `parent_root == hash_tree_root(latest_block_header)` check, the new
    header's `body_root`, and the post-state-root check in
    `state_transition`. Where upstream records
    `hash_tree_root(parent_header)` (history append, genesis anchoring),
    the block's `parent_root` is used instead — upstream verifies the two
    are equal before using them interchangeably.
  - Python `assert`s (internal invariants, not spec rejections) are not
    modeled: the zero-hash check on `justifications_roots`, the strict-zip
    length check, and the root-presence check before pruning (a missing
    root simply drops the entry).
  - The vote map `dict[Bytes32, list[Boolean]]` is an association list;
    the final re-pack sorts roots bytewise-lexicographically, matching
    Python's `sorted` on `bytes`.

Proves ST-1, ST-2, and ST-5 from `docs/lean4-proof-propositions.md`:
  - ST-1: `∀ s target, s.slot ≤ target →
      (State.processSlots s target).slot = target`.
  - ST-2: `State.processBlockHeader s b = .ok s' →
      s'.latestBlockHeader.slot = b.slot`.
  - ST-5: `State.transition` is a pure function — identical inputs yield
    identical outputs.
-/

import LeanSpec.Forks.Lstar.Config
import LeanSpec.Forks.Lstar.Containers.State
import LeanSpec.Forks.Lstar.Errors

namespace LeanSpec.Forks.Lstar

/-- Bytewise-lexicographic order on roots (Python `sorted` over `bytes`). -/
def byteListLe : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x < y || (x == y && byteListLe xs ys)

/-- `a ≤ b` on 32-byte roots, bytewise-lexicographic. -/
def Root.lexLe (a b : Root) : Bool :=
  byteListLe a.val.data.toList b.val.data.toList

namespace State

/-- Incrementing a slot strictly below some bound does not wrap around. -/
private theorem slot_succ_toNat {a b : Slot} (h : a < b) :
    (a + 1).toNat = a.toNat + 1 := by
  have h1 : a.toNat < b.toNat := UInt64.lt_iff_toNat_lt.mp h
  have h2 : b.toNat < 2 ^ 64 := b.toNat_lt
  rw [UInt64.toNat_add]
  have h3 : (1 : UInt64).toNat = 1 := rfl
  rw [h3, Nat.mod_eq_of_lt (by omega)]

/-- Generate a genesis state with empty history and proper initial values
(`generate_genesis`). Upstream sets `body_root` to the hash-tree root of
an empty block body; hash-free, it is zero here. -/
def generateGenesis (genesisTime : SSZ.Uint64) (validators : Validators) :
    State :=
  { config := { genesisTime := genesisTime }
    slot := 0
    latestBlockHeader := {
      slot := 0
      proposerIndex := 0
      parentRoot := SSZ.Bytes32.zero
      stateRoot := SSZ.Bytes32.zero
      bodyRoot := SSZ.Bytes32.zero }
    latestJustified := { root := SSZ.Bytes32.zero, slot := 0 }
    latestFinalized := { root := SSZ.Bytes32.zero, slot := 0 }
    historicalBlockHashes := #[]
    justifiedSlots := #[]
    validators := validators
    justificationsRoots := #[]
    justificationsValidators := #[] }

/-- Advance the state through empty slots up to `target`
(`process_slots`: `while state.slot < target_slot: state.slot += 1`). -/
def processSlots (s : State) (target : Slot) : State :=
  if _h : s.slot < target then
    processSlots { s with slot := s.slot + 1 } target
  else
    s
termination_by target.toNat - s.slot.toNat
decreasing_by
  show target.toNat - (s.slot + 1).toNat < target.toNat - s.slot.toNat
  have h1 : s.slot.toNat < target.toNat := UInt64.lt_iff_toNat_lt.mp _h
  rw [slot_succ_toNat _h]
  omega

/-- ST-1: empty-slot advancement makes `state.slot` equal `target`. -/
theorem process_slots_advances (s : State) (target : Slot)
    (h : s.slot ≤ target) :
    (processSlots s target).slot = target := by
  revert h
  induction s using processSlots.induct (target := target) with
  | case1 s hlt ih =>
    intro _
    rw [processSlots, dif_pos hlt]
    exact ih (by
      rw [UInt64.le_iff_toNat_le, slot_succ_toNat hlt]
      exact UInt64.lt_iff_toNat_lt.mp hlt)
  | case2 s hnlt =>
    intro h
    rw [processSlots, dif_neg hnlt]
    have h1 : s.slot.toNat ≤ target.toNat := UInt64.le_iff_toNat_le.mp h
    have h2 : ¬ s.slot.toNat < target.toNat :=
      fun hc => hnlt (UInt64.lt_iff_toNat_lt.mpr hc)
    exact UInt64.toNat_inj.mp (by omega)

/-- Validate the block header and update header-linked state
(`process_block_header`): the block must sit at the slot the state was
advanced to, be newer than the latest header, and come from the scheduled
round-robin proposer. Genesis is the chain's anchor, so the first block
forces its parent to justified and finalized. History and the
justified-slot tracking window are extended, then the block's header is
installed with zeroed roots (hash-free; see the module docstring). -/
def processBlockHeader (s : State) (b : Block) : ST.Result State :=
  if b.slot ≠ s.slot then
    .error (.invalidSlot s.slot b.slot)
  else if b.slot ≤ s.latestBlockHeader.slot then
    .error .headerSlotNotNewer
  else if s.validators.size = 0 then
    .error .emptyValidatorRegistry
  else if b.proposerIndex.toNat ≠ b.slot.toNat % s.validators.size then
    .error (.proposerMismatch
      (UInt64.ofNat (b.slot.toNat % s.validators.size)) b.proposerIndex)
  else
    -- Genesis is justified and finalized by definition, so the first block
    -- forces its parent to both; later blocks keep their checkpoints.
    let newJustified : Checkpoint :=
      if s.latestBlockHeader.slot = 0 then
        { root := b.parentRoot, slot := 0 }
      else s.latestJustified
    let newFinalized : Checkpoint :=
      if s.latestBlockHeader.slot = 0 then
        { root := b.parentRoot, slot := 0 }
      else s.latestFinalized
    -- Record the parent root, then a zero hash per slot skipped since the
    -- parent from missed proposals.
    let numEmptySlots := b.slot.toNat - s.latestBlockHeader.slot.toNat - 1
    let newHistory :=
      (s.historicalBlockHashes.push b.parentRoot) ++
        Array.replicate numEmptySlots SSZ.Bytes32.zero
    -- The current slot is not materialized until its header finishes, so
    -- the tracking window stops one short.
    let newJustifiedSlots :=
      JustifiedSlots.extendToSlot s.justifiedSlots newFinalized.slot (b.slot - 1)
    .ok { s with
      latestJustified := newJustified
      latestFinalized := newFinalized
      historicalBlockHashes := newHistory
      justifiedSlots := newJustifiedSlots
      latestBlockHeader := {
        slot := b.slot
        proposerIndex := b.proposerIndex
        parentRoot := b.parentRoot
        stateRoot := SSZ.Bytes32.zero
        bodyRoot := SSZ.Bytes32.zero } }

/-- ST-2: after applying a block header, the latest-header slot equals the
block slot. -/
theorem process_block_header_slot
    (s s' : State) (b : Block)
    (h : processBlockHeader s b = .ok s') :
    s'.latestBlockHeader.slot = b.slot := by
  unfold processBlockHeader at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · injection h with h'
          subst h'
          rfl

/-! ## Justification and finalization (`process_attestations`) -/

/-- Local accumulator for the attestation loop: the unpacked vote map plus
the checkpoint and tracking fields the loop advances. -/
structure JFAcc where
  justifications : List (Root × Array Bool)
  latestJustified : Checkpoint
  latestFinalized : Checkpoint
  justifiedSlots : JustifiedSlots

/-- Votes tallied so far for `r`, if any. -/
def lookupVotes (js : List (Root × Array Bool)) (r : Root) :
    Option (Array Bool) :=
  match js.find? (fun p => p.1 == r) with
  | some p => some p.2
  | none => none

/-- Replace (or add) the tally for `r`. -/
def insertVotes (js : List (Root × Array Bool)) (r : Root) (v : Array Bool) :
    List (Root × Array Bool) :=
  (r, v) :: js.filter (fun p => !(p.1 == r))

/-- Drop the tally for `r`. -/
def eraseVotes (js : List (Root × Array Bool)) (r : Root) :
    List (Root × Array Bool) :=
  js.filter (fun p => !(p.1 == r))

/-- Number of set bits in a tally. -/
def countTrue (votes : Array Bool) : Nat :=
  votes.foldl (fun n b => if b then n + 1 else n) 0

/-- Map an unfinalized root to its slot: the last index `i ≥ start` with
`hist[i] = r` (Python builds a dict by enumeration, so later occurrences
win). Used to prune tallies once their root is at or below the new
finalized boundary. -/
def rootToSlot (hist : Array Root) (start : Nat) (r : Root) : Option Nat :=
  (List.range (hist.size - start)).foldl
    (fun acc k => if hist[start + k]! == r then some (start + k) else acc)
    none

/-- No justifiable slot sits strictly between `src` and `tgt` relative to
the `finalized` boundary (the 3SF-mini finalization condition). -/
def noJustifiableBetween (finalized src tgt : Nat) : Bool :=
  (List.range (tgt - src - 1)).all fun k =>
    !(Slot.justifiableDelta (src + 1 + k - finalized))

/-- Advance justification (and possibly finalization) for a target that
reached the 2/3 supermajority: move `latestJustified` forward only, mark
the target's tracked bit, drop its tally, and — when the source lies past
the old finalized slot with no justifiable slot in between — finalize the
source, rebasing the tracking window and pruning dead tallies. -/
def applyJustification (rootSlot : Root → Option Nat) (acc : JFAcc)
    (src tgt : Checkpoint) : JFAcc :=
  let finalized := acc.latestFinalized.slot
  let acc₁ : JFAcc := { acc with
    latestJustified :=
      if acc.latestJustified.slot < tgt.slot then tgt else acc.latestJustified
    justifiedSlots :=
      match Slot.justifiedIndexAfter finalized tgt.slot with
      | some i => acc.justifiedSlots.setIfInBounds i true
      | none => acc.justifiedSlots
    justifications := eraseVotes acc.justifications tgt.root }
  if finalized < src.slot ∧
      noJustifiableBetween finalized.toNat src.slot.toNat tgt.slot.toNat then
    let delta := src.slot.toNat - finalized.toNat
    { acc₁ with
      latestFinalized := src
      justifiedSlots := acc₁.justifiedSlots.extract delta acc₁.justifiedSlots.size
      justifications := acc₁.justifications.filter fun p =>
        match rootSlot p.1 with
        | some sl => decide (src.slot.toNat < sl)
        | none => false }
  else acc₁

/-- Apply one aggregated attestation to the accumulator: the vote filters
(`continue` upstream) return the accumulator unchanged; bit-validation
failures reject the block; a tallied vote either stores the updated tally
or, on supermajority, advances justification. -/
def processAttestation (validatorCount : Nat) (hist : Array Root)
    (rootSlot : Root → Option Nat) (acc : JFAcc)
    (att : AggregatedAttestation) : ST.Result JFAcc :=
  let src := att.data.source
  let tgt := att.data.target
  let finalized := acc.latestFinalized.slot
  -- A vote may only anchor on an already-justified source.
  match JustifiedSlots.isSlotJustified acc.justifiedSlots finalized src.slot with
  | .error e => .error e
  | .ok false => .ok acc
  | .ok true =>
  -- An already-justified target gains nothing from more votes.
  match JustifiedSlots.isSlotJustified acc.justifiedSlots finalized tgt.slot with
  | .error e => .error e
  | .ok true => .ok acc
  | .ok false =>
  -- Both roots must match the canonical chain.
  if !(att.data.liesOnChain hist) then .ok acc
  -- The target must lie strictly after the source.
  else if tgt.slot ≤ src.slot then .ok acc
  -- The target must be at a justifiable distance from the finalized slot.
  else if !(Slot.isJustifiableAfter finalized tgt.slot) then .ok acc
  else
    let indices := AggregationBits.toValidatorIndices att.aggregationBits
    if indices.isEmpty then .error .emptyAggregationBits
    else if indices.any (fun i => decide (validatorCount ≤ i)) then
      .error .validatorIndexOutOfRange
    else
      let votes := (lookupVotes acc.justifications tgt.root).getD
        (Array.replicate validatorCount false)
      let votes := indices.foldl (fun v i => v.setIfInBounds i true) votes
      -- Threshold: justified once two-thirds of validators vote for the
      -- target (compared as integers: 3 · votes ≥ 2 · total).
      if 3 * countTrue votes < 2 * validatorCount then
        .ok { acc with
          justifications := insertVotes acc.justifications tgt.root votes }
      else
        .ok (applyJustification rootSlot acc src tgt)

/-- Split the flat SSZ vote layout into a per-root tally list. -/
def unpackJustifications (roots : JustificationRoots)
    (bits : JustificationValidators) (validatorCount : Nat) :
    List (Root × Array Bool) :=
  (List.range roots.size).map fun i =>
    (roots[i]!, bits.extract (i * validatorCount) ((i + 1) * validatorCount))

/-- Apply attestations and update justification and finalization under
3SF-mini rules (`process_attestations`). -/
def processAttestations (s : State)
    (attestations : List AggregatedAttestation) : ST.Result State :=
  -- Cap the distinct attestation data a block may carry.
  let distinct := (attestations.map (·.data)).eraseDups
  if MAX_ATTESTATIONS_DATA < distinct.length then
    .error (.tooManyAttestationData distinct.length MAX_ATTESTATIONS_DATA)
  else
    let validatorCount := s.validators.size
    let init : JFAcc := {
      justifications :=
        unpackJustifications s.justificationsRoots s.justificationsValidators
          validatorCount
      latestJustified := s.latestJustified
      latestFinalized := s.latestFinalized
      justifiedSlots := s.justifiedSlots }
    let rootSlot :=
      rootToSlot s.historicalBlockHashes (s.latestFinalized.slot.toNat + 1)
    match attestations.foldlM
        (processAttestation validatorCount s.historicalBlockHashes rootSlot)
        init with
    | .error e => .error e
    | .ok acc =>
      -- Re-pack the vote map into the flat SSZ layout, roots sorted for a
      -- deterministic representation across nodes.
      let sortedRoots := (acc.justifications.map (·.1)).mergeSort Root.lexLe
      .ok { s with
        latestJustified := acc.latestJustified
        latestFinalized := acc.latestFinalized
        justifiedSlots := acc.justifiedSlots
        justificationsRoots := sortedRoots.toArray
        justificationsValidators := sortedRoots.foldl
          (fun a r => a ++ ((lookupVotes acc.justifications r).getD #[])) #[] }

/-- Apply full block processing including header and body
(`process_block`). -/
def processBlock (s : State) (b : Block) : ST.Result State :=
  match processBlockHeader s b with
  | .error e => .error e
  | .ok s₁ => processAttestations s₁ b.body.attestations.toList

/-- Apply the complete state transition function for a block
(`state_transition`). Rejects a block whose slot is not strictly in the
future (`BLOCK_SLOT_NOT_IN_FUTURE`, raised upstream inside
`process_slots`), advances empty slots, then applies the block. The
post-state-root check needs `hash_tree_root` and is omitted (see the
module docstring). -/
def transition (s : State) (b : Block) : ST.Result State :=
  if b.slot ≤ s.slot then
    .error (.slotNotInFuture s.slot b.slot)
  else
    processBlock (processSlots s b.slot) b

/-- ST-5: the state transition function is pure — identical inputs always
yield identical outputs. Lean `def`s are pure by construction, so the
proof is `rfl`; the theorem records the meta-property the catalog tracks
and is usable by future composition proofs. -/
@[simp] theorem state_transition_pure (s : State) (b : Block) :
    transition s b = transition s b := rfl

end State
end LeanSpec.Forks.Lstar
