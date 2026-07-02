/-
State transition function — empty-slot advancement.

Mirrors `src/lean_spec/spec/forks/lstar/state_transition.py` in leanSpec:
  - `process_slots(state, target_slot)`: while `state.slot < target_slot`,
    advance `state.slot` by one.

Divergences from Python, documented per function:
  - `process_slots` upstream raises `BLOCK_SLOT_NOT_IN_FUTURE` when
    `target_slot ≤ state.slot`; in Lean `processSlots` is total (it returns
    the state unchanged) and that guard lives in `State.transition` (ST-5),
    matching where `state_transition` consumes it.
  - The pre-block state-root caching into `latest_block_header.state_root`
    is omitted until `hash_tree_root` instances land (needed by ST-3/ST-6);
    it touches a different field and does not affect the ST-1 property.

Proves ST-1 from `docs/lean4-proof-propositions.md`:
  - ST-1: `∀ s target, s.slot ≤ target →
      (State.processSlots s target).slot = target`.
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

end State
end LeanSpec.Forks.Lstar
