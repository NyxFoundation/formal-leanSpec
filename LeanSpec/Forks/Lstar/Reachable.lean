/-
Reachable states and their invariants.

A state is *reachable* when it arises from some genesis state
(`generate_genesis` in `src/lean_spec/spec/forks/lstar/state_transition.py`)
by a finite sequence of successful state transitions. The predicate has no
single Python counterpart — it is the meta-level closure of
`state_transition` that reachable-state invariants (catalog ST-4) are
stated against.

Proves ST-4 from `docs/lean4-proof-propositions.md`:
  - ST-4: `∀ s, Reachable s →
      s.latestJustified.slot ≥ s.latestFinalized.slot`.

Also proves that every reachable state is anchor-well-formed (`AnchorWF`),
which discharges the extra hypothesis of ST-3 / ST-6 and yields the
hypothesis-free corollaries `checkpoint_monotone_of_reachable` and
`finalization_irreversible_of_reachable`.
-/

import LeanSpec.Forks.Lstar.StateTransition

namespace LeanSpec.Forks.Lstar

/-- States reachable from some genesis by successful transitions. -/
inductive Reachable : State → Prop where
  | genesis (genesisTime : SSZ.Uint64) (validators : Validators) :
      Reachable (State.generateGenesis genesisTime validators)
  | step {s s' : State} (b : Block)
      (hs : Reachable s)
      (htrans : State.transition s b = .ok s') :
      Reachable s'

/-- Every reachable state is anchor-well-formed: at genesis both
checkpoints sit at slot 0, and after any block the latest header's slot is
the block's strictly positive slot, so the premise is vacuous. -/
theorem anchorWF_of_reachable {s : State} (h : Reachable s) :
    State.AnchorWF s := by
  induction h with
  | genesis genesisTime validators =>
    intro _
    exact ⟨rfl, rfl⟩
  | step b hs htrans ih =>
    intro hz
    exfalso
    have hdr := State.transition_header_slot _ _ b htrans
    have hlt := State.transition_slot_lt _ _ b htrans
    have hb : b.slot = 0 := by rw [← hdr, hz]
    rw [hb] at hlt
    have h1 := UInt64.lt_iff_toNat_lt.mp hlt
    have h0 : (0 : UInt64).toNat = 0 := rfl
    omega

/-- ST-4: the justified slot is always at least the finalized slot on every
state reachable from genesis. -/
theorem justified_ge_finalized (s : State) (hreach : Reachable s) :
    s.latestJustified.slot ≥ s.latestFinalized.slot := by
  induction hreach with
  | genesis genesisTime validators => exact UInt64.le_refl _
  | step b hs htrans ih => exact State.transition_jf _ _ b htrans ih

/-- ST-3 in catalog form for reachable states: the `AnchorWF` hypothesis is
discharged by reachability. -/
theorem checkpoint_monotone_of_reachable
    (s s' : State) (b : Block)
    (hreach : Reachable s)
    (h : State.transition s b = .ok s') :
    s.latestJustified.slot ≤ s'.latestJustified.slot ∧
    s.latestFinalized.slot ≤ s'.latestFinalized.slot :=
  State.checkpoint_monotone s s' b (anchorWF_of_reachable hreach) h

/-- ST-6 in catalog form for reachable states. -/
theorem finalization_irreversible_of_reachable
    (s s' : State) (b : Block)
    (hreach : Reachable s)
    (h : State.transition s b = .ok s') :
    s.latestFinalized.slot ≤ s'.latestFinalized.slot :=
  State.finalization_irreversible s s' b (anchorWF_of_reachable hreach) h

end LeanSpec.Forks.Lstar
