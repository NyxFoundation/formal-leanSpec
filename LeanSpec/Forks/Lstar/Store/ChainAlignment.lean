/-
The history-alignment layer of the fork-choice store (FC-8).

FC-7 (`Store/OnBlock.lean`) preserved the store invariants under a
residual hypothesis `hjnew`: an STF-advanced justified checkpoint names
an imported block at its own slot, and descends from the finalized
checkpoint. This file discharges the first half from a store invariant
and leaves the second as the explicit quorum-level assumption:

  - `Store.ChainAligned` — every stored post-state's
    `historical_block_hashes` mirrors the block map: the history is
    sized to the state's slot, each non-zero entry is a stored block
    root sitting at exactly that slot, and no stored state's justified
    slot exceeds the store's. `on_block` maintains all of it
    (`applyBlock_chainAligned`): the new state's history is the
    parent's plus the parent root plus zero hashes
    (`State.transition_hist`), and the justified checkpoint moves only
    onto that history (`State.transition_justified_on_chain`).
  - `applyBlock_justified_stored` — the discharged half of `hjnew`.
  - `onBlock_invariants` — FC-8: `on_block` preserves
    `WellFormed ∧ Aligned ∧ ChainAligned`, with the descent half of
    `hjnew` (`hjdesc`) as the one remaining hypothesis. That half is
    *not* a history fact: a competing fork's state can justify a
    checkpoint off the finalized subtree unless a 2/3 quorum argument
    (accountable safety) excludes conflicting supermajorities — the
    known open layer of the catalog, out of FC-8's scope.
-/

import LeanSpec.Forks.Lstar.HistoryAlignment
import LeanSpec.Forks.Lstar.Store.OnBlock

namespace LeanSpec.Forks.Lstar
namespace Store

/-! ## Indexing the extended history -/

private theorem pushRep_get_old (A : Array Root) (x : Root) (k i : Nat)
    (hi : i < A.size) :
    ((A.push x) ++ Array.replicate k SSZ.Bytes32.zero)[i]! = A[i]! := by
  have h1 : i < (A.push x).size := by
    rw [Array.size_push]; omega
  have h2 : i < ((A.push x) ++ Array.replicate k SSZ.Bytes32.zero).size := by
    rw [Array.size_append, Array.size_push]; omega
  rw [getElem!_pos _ i h2, getElem!_pos _ i hi]
  rw [Array.getElem_append_left h1]
  exact Array.getElem_push_lt hi

private theorem pushRep_get_boundary (A : Array Root) (x : Root) (k : Nat) :
    ((A.push x) ++ Array.replicate k SSZ.Bytes32.zero)[A.size]! = x := by
  have h1 : A.size < (A.push x).size := by
    rw [Array.size_push]; omega
  have h2 : A.size
      < ((A.push x) ++ Array.replicate k SSZ.Bytes32.zero).size := by
    rw [Array.size_append, Array.size_push]; omega
  rw [getElem!_pos ((A.push x) ++ Array.replicate k SSZ.Bytes32.zero)
    A.size h2]
  rw [Array.getElem_append_left h1]
  exact Array.getElem_push_eq

private theorem pushRep_get_high (A : Array Root) (x : Root) (k i : Nat)
    (hlo : A.size < i) (hhi : i < A.size + 1 + k) :
    ((A.push x) ++ Array.replicate k SSZ.Bytes32.zero)[i]!
      = SSZ.Bytes32.zero := by
  have h2 : i < ((A.push x) ++ Array.replicate k SSZ.Bytes32.zero).size := by
    rw [Array.size_append, Array.size_push, Array.size_replicate]; omega
  have h1 : (A.push x).size ≤ i := by
    rw [Array.size_push]; omega
  rw [getElem!_pos ((A.push x) ++ Array.replicate k SSZ.Bytes32.zero) i h2]
  rw [Array.getElem_append_right h1]
  exact Array.getElem_replicate ..

/-! ## The chain-alignment invariant -/

/-- Every stored post-state's history mirrors the block map (FC-8):
histories are sized to their state's slot, every non-zero entry names a
stored block at exactly that slot, and no stored state's justified slot
outruns the store's. `on_block` maintains all four clauses. -/
structure ChainAligned (st : Store) : Prop where
  /-- A stored history is sized to its header slot (one entry per past
  slot). -/
  histSize : ∀ r s₀, st.getState? r = some s₀ →
    s₀.historicalBlockHashes.size = s₀.latestBlockHeader.slot.toNat
  /-- A stored post-state sits at its header's slot. -/
  slotHeader : ∀ r s₀, st.getState? r = some s₀ →
    s₀.slot = s₀.latestBlockHeader.slot
  /-- `on_block` advances the store's justified checkpoint over every
  imported state, so no stored state's justified slot exceeds it. -/
  statesJustifiedDominated : ∀ r s₀, st.getState? r = some s₀ →
    s₀.latestJustified.slot ≤ st.latestJustified.slot
  /-- Every non-zero history entry names a stored block sitting at
  exactly that slot. -/
  histAligned : ∀ r s₀, st.getState? r = some s₀ →
    ∀ i, i < s₀.historicalBlockHashes.size →
      s₀.historicalBlockHashes[i]! ≠ SSZ.Bytes32.zero →
      ∃ blk, st.getBlock? (s₀.historicalBlockHashes[i]!) = some blk ∧
        blk.slot.toNat = i

/-- `ChainAligned` reads only blocks, states, and the justified
checkpoint. -/
theorem chainAligned_congr {st st' : Store}
    (hb : st'.blocks = st.blocks) (hs : st'.states = st.states)
    (hj : st'.latestJustified = st.latestJustified)
    (hcal : ChainAligned st) : ChainAligned st' := by
  have hgb : ∀ r, st'.getBlock? r = st.getBlock? r := by
    intro r; unfold getBlock?; rw [hb]
  have hgs : ∀ r, st'.getState? r = st.getState? r := by
    intro r; unfold getState?; rw [hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s₀ h1
    rw [hgs r] at h1
    exact hcal.histSize r s₀ h1
  · intro r s₀ h1
    rw [hgs r] at h1
    exact hcal.slotHeader r s₀ h1
  · intro r s₀ h1
    rw [hgs r] at h1
    rw [hj]
    exact hcal.statesJustifiedDominated r s₀ h1
  · intro r s₀ h1 i hi hnz
    rw [hgs r] at h1
    obtain ⟨blk, hlook, hslot⟩ := hcal.histAligned r s₀ h1 i hi hnz
    exact ⟨blk, by rw [hgb]; exact hlook, hslot⟩

/-! ## `advance_to` slot bounds -/

private theorem advanceTo_slot_ge_self (self c : Checkpoint) :
    self.slot ≤ (self.advanceTo c).slot := by
  unfold Checkpoint.advanceTo
  by_cases hlt : self.slot < c.slot
  · rw [if_pos hlt]
    exact UInt64.le_of_lt hlt
  · rw [if_neg hlt]
    exact UInt64.le_refl _

private theorem advanceTo_slot_ge_cand (self c : Checkpoint) :
    c.slot ≤ (self.advanceTo c).slot := by
  unfold Checkpoint.advanceTo
  by_cases hlt : self.slot < c.slot
  · rw [if_pos hlt]
    exact UInt64.le_refl _
  · rw [if_neg hlt]
    exact UInt64.not_lt.mp hlt

/-! ## Preservation through the import writes -/

/-- The import writes preserve the chain alignment: the new state's
history is the parent's plus the parent root plus zero hashes, all of
which the grown block map covers; every old entry transfers untouched. -/
theorem applyBlock_chainAligned (st : Store) (blockRoot : Root) (b : Block)
    (parentState postState : State)
    (hwf : WellFormed st) (hal : Aligned st) (hcal : ChainAligned st)
    (hfreshB : st.getBlock? blockRoot = none)
    (hfreshS : st.getState? blockRoot = none)
    (hparent : st.getState? b.parentRoot = some parentState)
    (htrans : State.transition parentState b = .ok postState) :
    ChainAligned (applyBlock st blockRoot b postState) := by
  have hgb := applyBlock_getBlock? st blockRoot b postState
  have hgs := applyBlock_getState? st blockRoot b postState
  have hparentNe : b.parentRoot ≠ blockRoot := by
    intro heq
    rw [heq, hfreshS] at hparent
    cases hparent
  obtain ⟨pb, hpb⟩ := Option.isSome_iff_exists.mp
    ((hwf.blocksStatesAligned b.parentRoot).mpr (by rw [hparent]; rfl))
  have hpbslot : parentState.slot = pb.slot :=
    hal.statesSlotAligned b.parentRoot pb parentState hpb hparent
  have hpsz := hcal.histSize b.parentRoot parentState hparent
  have hpsh := hcal.slotHeader b.parentRoot parentState hparent
  have hsize := State.transition_hist_size parentState postState b htrans
    hpsz
  have hhist := State.transition_hist parentState postState b htrans
  -- An entry stored in the old map is found unchanged in the new one.
  have htransfer : ∀ (rt : Root) (blk : Block),
      st.getBlock? rt = some blk →
      (applyBlock st blockRoot b postState).getBlock? rt = some blk := by
    intro rt blk hlk
    rw [hgb rt]
    by_cases hr : (blockRoot == rt) = true
    · exfalso
      rw [eq_of_beq hr, hlk] at hfreshB
      cases hfreshB
    · rw [if_neg hr]
      exact hlk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s₀ h1
    rw [hgs r] at h1
    by_cases hr : (blockRoot == r) = true
    · rw [if_pos hr] at h1
      injection h1 with h1'
      rw [← h1']
      rw [State.transition_header_slot parentState postState b htrans]
      exact hsize
    · rw [if_neg hr] at h1
      exact hcal.histSize r s₀ h1
  · intro r s₀ h1
    rw [hgs r] at h1
    by_cases hr : (blockRoot == r) = true
    · rw [if_pos hr] at h1
      injection h1 with h1'
      rw [← h1']
      rw [State.transition_header_slot parentState postState b htrans]
      exact State.transition_state_slot parentState postState b htrans
    · rw [if_neg hr] at h1
      exact hcal.slotHeader r s₀ h1
  · intro r s₀ h1
    rw [hgs r] at h1
    by_cases hr : (blockRoot == r) = true
    · rw [if_pos hr] at h1
      injection h1 with h1'
      rw [← h1']
      exact advanceTo_slot_ge_cand st.latestJustified
        postState.latestJustified
    · rw [if_neg hr] at h1
      exact UInt64.le_trans (hcal.statesJustifiedDominated r s₀ h1)
        (advanceTo_slot_ge_self st.latestJustified
          postState.latestJustified)
  · intro r s₀ h1 i hi hnz
    rw [hgs r] at h1
    by_cases hr : (blockRoot == r) = true
    · -- The new state's history: parent entries, the parent root, or
      -- zero hashes.
      rw [if_pos hr] at h1
      injection h1 with h1'
      subst h1'
      rw [hhist] at hi hnz ⊢
      rw [Array.size_append, Array.size_push, Array.size_replicate] at hi
      by_cases hcase : i < parentState.historicalBlockHashes.size
      · rw [pushRep_get_old _ _ _ _ hcase] at hnz ⊢
        obtain ⟨blk, hlook, hslot⟩ :=
          hcal.histAligned b.parentRoot parentState hparent i hcase hnz
        exact ⟨blk, htransfer _ _ hlook, hslot⟩
      · by_cases hcase2 : i = parentState.historicalBlockHashes.size
        · subst hcase2
          rw [pushRep_get_boundary] at hnz ⊢
          refine ⟨pb, htransfer _ _ hpb, ?_⟩
          have h1 := congrArg UInt64.toNat hpbslot
          have h2 := congrArg UInt64.toNat hpsh
          omega
        · have hlo : parentState.historicalBlockHashes.size < i := by
            omega
          rw [pushRep_get_high _ _ _ _ hlo (by omega)] at hnz
          exact absurd rfl hnz
    · rw [if_neg hr] at h1
      obtain ⟨blk, hlook, hslot⟩ := hcal.histAligned r s₀ h1 i hi hnz
      exact ⟨blk, htransfer _ _ hlook, hslot⟩

/-! ## Discharging the stored half of FC-7's `hjnew` -/

/-- The STF-advanced justified checkpoint names a block the import
store knows, at exactly its own slot: the checkpoint lies on the
post-history (`transition_justified_on_chain`), and the history mirrors
the block map (`ChainAligned` plus the parent root for the boundary
entry). -/
theorem applyBlock_justified_stored (st : Store) (blockRoot : Root)
    (b : Block) (parentState postState : State)
    (hwf : WellFormed st) (hal : Aligned st) (hcal : ChainAligned st)
    (hfreshB : st.getBlock? blockRoot = none)
    (hparent : st.getState? b.parentRoot = some parentState)
    (htrans : State.transition parentState b = .ok postState)
    (hlt : st.latestJustified.slot < postState.latestJustified.slot) :
    ∃ bj, (applyBlock st blockRoot b postState).getBlock?
        postState.latestJustified.root = some bj ∧
      bj.slot = postState.latestJustified.slot := by
  obtain ⟨pb, hpb⟩ := Option.isSome_iff_exists.mp
    ((hwf.blocksStatesAligned b.parentRoot).mpr (by rw [hparent]; rfl))
  have hpbslot : parentState.slot = pb.slot :=
    hal.statesSlotAligned b.parentRoot pb parentState hpb hparent
  have hpsz := hcal.histSize b.parentRoot parentState hparent
  have hpsh := hcal.slotHeader b.parentRoot parentState hparent
  have hhist := State.transition_hist parentState postState b htrans
  have htransfer : ∀ (rt : Root) (blk : Block),
      st.getBlock? rt = some blk →
      (applyBlock st blockRoot b postState).getBlock? rt = some blk := by
    intro rt blk hlk
    rw [applyBlock_getBlock?]
    by_cases hr : (blockRoot == rt) = true
    · exfalso
      rw [eq_of_beq hr, hlk] at hfreshB
      cases hfreshB
    · rw [if_neg hr]
      exact hlk
  cases State.transition_justified_on_chain parentState postState b
      htrans with
  | inl heq =>
    exfalso
    have hdom := hcal.statesJustifiedDominated b.parentRoot parentState
      hparent
    rw [heq] at hlt
    have h1 := UInt64.lt_iff_toNat_lt.mp hlt
    have h2 := UInt64.le_iff_toNat_le.mp hdom
    omega
  | inr h2 =>
    cases h2 with
    | inl hz =>
      exfalso
      rw [hz] at hlt
      have h1 := UInt64.lt_iff_toNat_lt.mp hlt
      have h0 : (0 : UInt64).toNat = 0 := rfl
      omega
    | inr hoc =>
      obtain ⟨hnz, hbound, hidx⟩ := hoc
      rw [hhist] at hbound hidx
      rw [Array.size_append, Array.size_push, Array.size_replicate]
        at hbound
      by_cases hcase :
          postState.latestJustified.slot.toNat
            < parentState.historicalBlockHashes.size
      · rw [pushRep_get_old _ _ _ _ hcase] at hidx
        have hnz' :
            parentState.historicalBlockHashes[
              postState.latestJustified.slot.toNat]! ≠ SSZ.Bytes32.zero :=
          by rw [hidx]; exact hnz
        obtain ⟨blk, hlook, hslot⟩ := hcal.histAligned b.parentRoot
          parentState hparent postState.latestJustified.slot.toNat hcase
          hnz'
        rw [hidx] at hlook
        exact ⟨blk, htransfer _ _ hlook,
          UInt64.toNat_inj.mp (by omega)⟩
      · by_cases hcase2 :
            postState.latestJustified.slot.toNat
              = parentState.historicalBlockHashes.size
        · rw [hcase2, pushRep_get_boundary] at hidx
          refine ⟨pb, ?_, ?_⟩
          · rw [← hidx]
            exact htransfer _ _ hpb
          · have h1 := congrArg UInt64.toNat hpbslot
            have h2 := congrArg UInt64.toNat hpsh
            exact UInt64.toNat_inj.mp (by omega)
        · have hlo : parentState.historicalBlockHashes.size
              < postState.latestJustified.slot.toNat := by omega
          rw [pushRep_get_high _ _ _ _ hlo (by omega)] at hidx
          exact absurd hidx.symm hnz

/-! ## FC-8: `on_block` preserves the chain alignment -/

/-- FC-8: a successful `on_block` preserves
`WellFormed ∧ Aligned ∧ ChainAligned`. The stored half of FC-7's
`hjnew` is discharged by the chain alignment; the descent half stays as
`hjdesc`, the quorum-level assumption (see the module docstring). -/
theorem onBlock_invariants [SSZ.HasHashTreeRoot AttestationData]
    (prune : Store → Store)
    (hprune : ∀ s, (prune s).blocks = s.blocks ∧
      (prune s).states = s.states ∧
      (prune s).latestJustified = s.latestJustified ∧
      (prune s).latestFinalized = s.latestFinalized)
    (st st' : Store) (blockRoot : Root) (b : Block)
    (hwf : WellFormed st) (hal : Aligned st) (hcal : ChainAligned st)
    (hfreshParent : ∀ p ∈ st.blocks, p.2.parentRoot ≠ blockRoot)
    (hjdesc : ∀ parentState postState,
      st.getState? b.parentRoot = some parentState →
      State.transition parentState b = .ok postState →
      st.latestJustified.slot < postState.latestJustified.slot →
      checkpointIsAncestor (applyBlock st blockRoot b postState)
        st.latestFinalized postState.latestJustified = true)
    (h : onBlock prune st blockRoot b = .ok st') :
    WellFormed st' ∧ Aligned st' ∧ ChainAligned st' := by
  unfold onBlock at h
  split at h
  · injection h with h'
    subst h'
    exact ⟨hwf, hal, hcal⟩
  · next hknown =>
    have hfreshB : st.getBlock? blockRoot = none :=
      Option.not_isSome_iff_eq_none.mp hknown
    have hfreshS : st.getState? blockRoot = none := by
      cases hs : st.getState? blockRoot with
      | none => rfl
      | some s₀ =>
        exfalso
        have := (hwf.blocksStatesAligned blockRoot).mpr (by rw [hs]; rfl)
        rw [hfreshB] at this
        cases this
    split at h
    · simp at h
    · next parentState hparent =>
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · next postState htrans =>
              have hjcond :
                  st.latestJustified.slot
                      < postState.latestJustified.slot →
                  (∃ bj, (applyBlock st blockRoot b
                      postState).getBlock?
                      postState.latestJustified.root = some bj ∧
                    bj.slot = postState.latestJustified.slot) ∧
                  checkpointIsAncestor
                    (applyBlock st blockRoot b postState)
                    st.latestFinalized postState.latestJustified
                    = true :=
                fun hlt =>
                  ⟨applyBlock_justified_stored st blockRoot b
                      parentState postState hwf hal hcal hfreshB
                      hparent htrans hlt,
                    hjdesc parentState postState hparent htrans hlt⟩
              obtain ⟨hwf₁, hal₁⟩ := applyBlock_invariants st blockRoot
                b parentState postState hwf hal hfreshB hfreshS hparent
                htrans hfreshParent hjcond
              have hcal₁ := applyBlock_chainAligned st blockRoot b
                parentState postState hwf hal hcal hfreshB hfreshS
                hparent htrans
              have hwf₂ :
                  WellFormed (updateHead
                    (applyBlock st blockRoot b postState)) :=
                updateHead_wellFormed _ hwf₁ hal₁.justifiedSlotMatches
                  hal₁.statesDominated
              have hal₂ :
                  Aligned (updateHead
                    (applyBlock st blockRoot b postState)) :=
                aligned_congr
                  (st := applyBlock st blockRoot b postState)
                  rfl rfl rfl hal₁
              have hcal₂ :
                  ChainAligned (updateHead
                    (applyBlock st blockRoot b postState)) :=
                chainAligned_congr
                  (st := applyBlock st blockRoot b postState)
                  rfl rfl rfl hcal₁
              dsimp only at h
              injection h with h'
              subst h'
              split
              · obtain ⟨hpb', hps', hpj', hpf'⟩ :=
                  hprune (updateHead (applyBlock st blockRoot b
                    postState))
                exact ⟨wellFormed_congr hpb' hps' hpj' hpf' hwf₂,
                  aligned_congr hpb' hps' hpj' hal₂,
                  chainAligned_congr hpb' hps' hpj' hcal₂⟩
              · exact ⟨hwf₂, hal₂, hcal₂⟩

end Store
end LeanSpec.Forks.Lstar
