/-
History alignment of the state transition.

Mirrors the history-facing behavior of
`src/lean_spec/spec/forks/lstar/state_transition.py`:
  - `process_block_header` appends the parent root and one zero hash per
    skipped slot to `historical_block_hashes`; no other stage touches
    the history.
  - `process_attestations` moves `latest_justified` only to the target
    of a vote that passed the `lies_on_chain` filter — a checkpoint
    whose root is the (non-zero) history entry at its own slot.

These are the state-transition halves of the FC-8 store invariant
(`Store.ChainAligned`, `LeanSpec/Forks/Lstar/Store/ChainAlignment.lean`):
the history mirrors the block map, so an STF-advanced justified
checkpoint names an imported block at its own slot.

Supports FC-8 from `docs/lean4-proof-propositions.md`:
  - `transition_hist` / `transition_hist_size` and the indexed forms —
    the post-history is the parent history, then the parent root, then
    zero hashes.
  - `transition_justified_on_chain` — the post-justified checkpoint is
    the parent's, the genesis anchor (slot 0), or lies on the
    post-history at its own slot with a non-zero root.
-/

import LeanSpec.Forks.Lstar.StateTransition

namespace LeanSpec.Forks.Lstar
namespace State

/-! ## History preservation of the non-header stages -/

/-- `processSlots` only advances `slot`; the history is untouched. -/
theorem processSlots_hist (s : State) (target : Slot) :
    (processSlots s target).historicalBlockHashes
      = s.historicalBlockHashes := by
  induction s using processSlots.induct (target := target) with
  | case1 s hlt ih =>
    rw [processSlots, dif_pos hlt]
    exact ih
  | case2 s hnlt =>
    rw [processSlots, dif_neg hnlt]

/-- `processAttestations` never touches the history. -/
theorem processAttestations_hist (s s' : State)
    (atts : List AggregatedAttestation)
    (h : processAttestations s atts = .ok s') :
    s'.historicalBlockHashes = s.historicalBlockHashes := by
  unfold processAttestations at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
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

/-! ## The header stage: history shape and the genesis anchor -/

/-- `processBlockHeader` extends the history with the parent root and
one zero hash per skipped slot. -/
theorem processBlockHeader_hist (s s' : State) (b : Block)
    (h : processBlockHeader s b = .ok s') :
    s'.historicalBlockHashes =
      (s.historicalBlockHashes.push b.parentRoot) ++
        Array.replicate
          (b.slot.toNat - s.latestBlockHeader.slot.toNat - 1)
          SSZ.Bytes32.zero := by
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

/-- The header stage keeps the justified checkpoint or anchors it at
slot 0 (the genesis anchor of the first block). -/
theorem processBlockHeader_justified_slot (s s' : State) (b : Block)
    (h : processBlockHeader s b = .ok s') :
    s'.latestJustified = s.latestJustified ∨
    s'.latestJustified.slot = 0 := by
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
          show (if s.latestBlockHeader.slot = 0 then
              ({ root := b.parentRoot, slot := 0 } : Checkpoint)
            else s.latestJustified) = s.latestJustified ∨
            (if s.latestBlockHeader.slot = 0 then
              ({ root := b.parentRoot, slot := 0 } : Checkpoint)
            else s.latestJustified).slot = 0
          split
          · exact .inr rfl
          · exact .inl rfl

/-- A successful header stage requires a strictly newer block slot. -/
theorem processBlockHeader_slot_lt (s s' : State) (b : Block)
    (h : processBlockHeader s b = .ok s') :
    s.latestBlockHeader.slot < b.slot := by
  unfold processBlockHeader at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next hle => exact UInt64.not_le.mp hle

/-! ## The justified checkpoint moves only onto the chain -/

/-- `liesOnChain` pins the target checkpoint to the history: its root
is non-zero, its slot indexes the history, and the entry there is
exactly its root. -/
theorem liesOnChain_target (d : AttestationData) (hist : Array Root)
    (h : d.liesOnChain hist = true) :
    d.target.root ≠ SSZ.Bytes32.zero ∧
    d.target.slot.toNat < hist.size ∧
    hist[d.target.slot.toNat]! = d.target.root := by
  unfold AttestationData.liesOnChain at h
  dsimp only at h
  split at h
  · simp at h
  · next hz =>
    split at h
    · simp at h
    · next hn =>
      have hz' : ¬(d.target.root == SSZ.Bytes32.zero) = true := by
        intro hc
        exact hz (by rw [hc]; simp)
      have hnz : d.target.root ≠ SSZ.Bytes32.zero := fun hc =>
        hz' (by rw [hc]; exact beq_self_eq_true _)
      have hbound : d.target.slot.toNat < hist.size := by
        by_cases hb : hist.size ≤ d.target.slot.toNat
        · exact absurd (Or.inr (Or.inl hb)) hn
        · omega
      have htgt : (d.target.root == hist[d.target.slot.toNat]!) = true :=
        ((Bool.and_eq_true ..).mp
          ((Bool.and_eq_true ..).mp h).1).2
      exact ⟨hnz, hbound, (eq_of_beq htgt).symm⟩

/-- `applyJustification` keeps the justified checkpoint or moves it to
the supermajority target. -/
theorem applyJustification_justified (rootSlot : Root → Option Nat)
    (acc : JFAcc) (src tgt : Checkpoint) :
    (applyJustification rootSlot acc src tgt).latestJustified
        = acc.latestJustified ∨
    (applyJustification rootSlot acc src tgt).latestJustified = tgt := by
  unfold applyJustification
  dsimp only
  split
  · split
    · exact .inr rfl
    · exact .inl rfl
  · split
    · exact .inr rfl
    · exact .inl rfl

/-- One attestation step keeps the justified checkpoint or moves it to
the target of a vote that passed the `lies_on_chain` filter. -/
theorem processAttestation_justified (validatorCount : Nat)
    (hist : Array Root) (rootSlot : Root → Option Nat) (acc acc' : JFAcc)
    (att : AggregatedAttestation)
    (h : processAttestation validatorCount hist rootSlot acc att
      = .ok acc') :
    acc'.latestJustified = acc.latestJustified ∨
    (att.data.liesOnChain hist = true ∧
      acc'.latestJustified = att.data.target) := by
  unfold processAttestation at h
  dsimp only at h
  split at h
  · simp at h
  · injection h with h'
    subst h'
    exact .inl rfl
  · split at h
    · simp at h
    · injection h with h'
      subst h'
      exact .inl rfl
    · split at h
      · injection h with h'
        subst h'
        exact .inl rfl
      · next hlies =>
        have hlies' : att.data.liesOnChain hist = true := by
          cases hx : att.data.liesOnChain hist with
          | true => rfl
          | false => exact absurd (by rw [hx]; rfl) hlies
        split at h
        · injection h with h'
          subst h'
          exact .inl rfl
        · split at h
          · injection h with h'
            subst h'
            exact .inl rfl
          · split at h
            · simp at h
            · split at h
              · simp at h
              · split at h
                · injection h with h'
                  subst h'
                  exact .inl rfl
                · injection h with h'
                  subst h'
                  cases applyJustification_justified rootSlot acc
                      att.data.source att.data.target with
                  | inl heq => exact .inl heq
                  | inr heq => exact .inr ⟨hlies', heq⟩

/-- Folding attestation steps: the justified checkpoint ends where it
started or on the target of some on-chain vote. -/
theorem foldlM_processAttestation_justified (validatorCount : Nat)
    (hist : Array Root) (rootSlot : Root → Option Nat) :
    ∀ (atts : List AggregatedAttestation) (acc acc' : JFAcc),
    List.foldlM (processAttestation validatorCount hist rootSlot) acc atts
      = .ok acc' →
    acc'.latestJustified = acc.latestJustified ∨
    ∃ d : AttestationData, d.liesOnChain hist = true ∧
      acc'.latestJustified = d.target
  | [], acc, acc', h => by
    injection h with h'
    subst h'
    exact .inl rfl
  | att :: atts, acc, acc', h => by
    rw [List.foldlM_cons] at h
    cases hstep : processAttestation validatorCount hist rootSlot acc att
        with
    | error e =>
      rw [hstep] at h
      injection h
    | ok acc₁ =>
      rw [hstep] at h
      have hrest :
          List.foldlM (processAttestation validatorCount hist rootSlot)
            acc₁ atts = .ok acc' := h
      have h2 := foldlM_processAttestation_justified validatorCount hist
        rootSlot atts acc₁ acc' hrest
      cases h2 with
      | inl heq =>
        cases processAttestation_justified validatorCount hist rootSlot
            acc acc₁ att hstep with
        | inl heq' => exact .inl (heq.trans heq')
        | inr hd => exact .inr ⟨att.data, hd.1, heq.trans hd.2⟩
      | inr hd => exact .inr hd

/-- `processAttestations`: the justified checkpoint stays or lands on
the target of an on-chain vote, judged against this state's history. -/
theorem processAttestations_justified (s s' : State)
    (atts : List AggregatedAttestation)
    (h : processAttestations s atts = .ok s') :
    s'.latestJustified = s.latestJustified ∨
    ∃ d : AttestationData,
      d.liesOnChain s.historicalBlockHashes = true ∧
      s'.latestJustified = d.target := by
  unfold processAttestations at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · next acc heq =>
            injection h with h'
            subst h'
            exact foldlM_processAttestation_justified _ _ _ atts _ acc heq

/-! ## Transition-level history alignment -/

/-- The post-history is the pre-history, then the parent root, then one
zero hash per skipped slot. -/
theorem transition_hist (s s' : State) (b : Block)
    (h : transition s b = .ok s') :
    s'.historicalBlockHashes =
      (s.historicalBlockHashes.push b.parentRoot) ++
        Array.replicate
          (b.slot.toNat - s.latestBlockHeader.slot.toNat - 1)
          SSZ.Bytes32.zero := by
  unfold transition at h
  split at h
  · simp at h
  · unfold processBlock at h
    split at h
    · simp at h
    · next s₁ hh =>
      have hps := processSlots_hist s b.slot
      have hpsc := processSlots_checkpoints s b.slot
      have hhdr := processBlockHeader_hist _ _ _ hh
      have hatt := processAttestations_hist _ _ _ h
      rw [hatt, hhdr, hps, hpsc.2.2]

/-- A successful transition sits strictly above the previous header. -/
theorem transition_header_lt (s s' : State) (b : Block)
    (h : transition s b = .ok s') :
    s.latestBlockHeader.slot < b.slot := by
  unfold transition at h
  split at h
  · simp at h
  · unfold processBlock at h
    split at h
    · simp at h
    · next s₁ hh =>
      have := processBlockHeader_slot_lt _ _ _ hh
      rw [(processSlots_checkpoints s b.slot).2.2] at this
      exact this

/-- With the pre-history sized to the pre-header slot, the post-history
is sized to the block's slot. -/
theorem transition_hist_size (s s' : State) (b : Block)
    (h : transition s b = .ok s')
    (hsz : s.historicalBlockHashes.size
      = s.latestBlockHeader.slot.toNat) :
    s'.historicalBlockHashes.size = b.slot.toNat := by
  rw [transition_hist s s' b h]
  rw [Array.size_append, Array.size_push, Array.size_replicate, hsz]
  have h1 := UInt64.lt_iff_toNat_lt.mp (transition_header_lt s s' b h)
  omega

/-- The transition keeps the justified checkpoint, anchors it at
slot 0, or lands it on the post-history at its own slot with a
non-zero root. -/
theorem transition_justified_on_chain (s s' : State) (b : Block)
    (h : transition s b = .ok s') :
    s'.latestJustified = s.latestJustified ∨
    s'.latestJustified.slot = 0 ∨
    (s'.latestJustified.root ≠ SSZ.Bytes32.zero ∧
      s'.latestJustified.slot.toNat < s'.historicalBlockHashes.size ∧
      s'.historicalBlockHashes[s'.latestJustified.slot.toNat]!
        = s'.latestJustified.root) := by
  unfold transition at h
  split at h
  · simp at h
  · unfold processBlock at h
    split at h
    · simp at h
    · next s₁ hh =>
      have hpsc := processSlots_checkpoints s b.slot
      have hatthist := processAttestations_hist _ _ _ h
      cases processAttestations_justified _ _ _ h with
      | inl heq =>
        cases processBlockHeader_justified_slot _ _ _ hh with
        | inl heq' =>
          exact .inl (by rw [heq, heq', hpsc.1])
        | inr hz => exact .inr (.inl (by rw [heq]; exact hz))
      | inr hd =>
        obtain ⟨d, hlies, htgt⟩ := hd
        obtain ⟨hnz, hbound, hidx⟩ :=
          liesOnChain_target d s₁.historicalBlockHashes hlies
        rw [hatthist]
        rw [htgt]
        exact .inr (.inr ⟨hnz, hbound, hidx⟩)

end State
end LeanSpec.Forks.Lstar
