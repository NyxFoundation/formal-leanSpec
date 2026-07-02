/-
State transition function — empty-slot advancement and header application.

Mirrors `src/lean_spec/spec/forks/lstar/state_transition.py` in leanSpec:
  - `process_slots(state, target_slot)`: while `state.slot < target_slot`,
    advance `state.slot` by one.
  - `process_block_header(state, block)`: validate the header checks and
    install the block as `latest_block_header`.

Divergences from Python, documented per function:
  - `process_slots` upstream raises `BLOCK_SLOT_NOT_IN_FUTURE` when
    `target_slot ≤ state.slot`; in Lean `processSlots` is total (it returns
    the state unchanged) and that guard lives in `State.transition` (ST-5),
    matching where `state_transition` consumes it.
  - The pre-block state-root caching into `latest_block_header.state_root`
    is omitted until `hash_tree_root` instances land (needed by ST-3/ST-6);
    it touches a different field and does not affect the ST-1 property.
  - `processBlockHeader` validates the slot checks only. The proposer check
    needs `validators` (absent from the minimal `State`; ST-3/ST-4), and the
    parent-root / body-root computations need `hash_tree_root` instances on
    `BlockHeader` / `BlockBody`; until then `parentRoot` is taken from the
    block unchecked and the new header's roots are zero. The
    genesis-anchoring checkpoint update and the history bookkeeping
    (`historical_block_hashes`, `justified_slots`) also wait for the full
    `State` (ST-3/ST-6).

Proves ST-1 and ST-2 from `docs/lean4-proof-propositions.md`:
  - ST-1: `∀ s target, s.slot ≤ target →
      (State.processSlots s target).slot = target`.
  - ST-2: `State.processBlockHeader s b = .ok s' →
      s'.latestBlockHeader.slot = b.slot`.
-/

import LeanSpec.Forks.Lstar.Containers.State
import LeanSpec.Forks.Lstar.Errors

namespace LeanSpec.Forks.Lstar
namespace State

/-- Incrementing a slot strictly below some bound does not wrap around. -/
private theorem slot_succ_toNat {a b : Slot} (h : a < b) :
    (a + 1).toNat = a.toNat + 1 := by
  have h1 : a.toNat < b.toNat := UInt64.lt_iff_toNat_lt.mp h
  have h2 : b.toNat < 2 ^ 64 := b.toNat_lt
  rw [UInt64.toNat_add]
  have h3 : (1 : UInt64).toNat = 1 := rfl
  rw [h3, Nat.mod_eq_of_lt (by omega)]

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
(`process_block_header`). Checks that the block sits at the slot the state
was advanced to and is newer than the latest header, then installs the
block's header with zeroed roots (see the module docstring for the
deferred checks). -/
def processBlockHeader (s : State) (b : Block) : ST.Result State :=
  if b.slot ≠ s.slot then
    .error (.invalidSlot s.slot b.slot)
  else if b.slot ≤ s.latestBlockHeader.slot then
    .error .headerSlotNotNewer
  else
    .ok { s with
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
    · injection h with h'
      subst h'
      rfl

end State
end LeanSpec.Forks.Lstar
