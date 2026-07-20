/-
Block import into the fork-choice store (`on_block`).

Mirrors `on_block` in `src/lean_spec/spec/forks/lstar/fork_choice.py`
(post leanEthereum/leanSpec#1182):
  - skip a block already in the store;
  - resolve the parent's post-state (`UNKNOWN_PARENT_BLOCK`);
  - bound the slot against the parent and the clock
    (`BLOCK_SLOT_GAP_TOO_LARGE`, `BLOCK_TOO_FAR_IN_FUTURE`, the #1182
    guards);
  - reject duplicate attestation data (`DUPLICATE_ATTESTATION_DATA`);
  - run the state transition, insert the block and its post-state,
    advance `latest_justified` via `Checkpoint.advance_to`, seed the
    block-carried votes into the known pool;
  - recompute the head (`update_head`, FC-6), and prune stale vote data
    when finalization advanced.

Divergences from Python, documented here:
  - `hash_tree_root(block)` is Arklib-side, so the block root enters as
    the `blockRoot` parameter.
  - `verify_signatures` is XMSS (Arklib-side) and aborts the import on
    failure; the model imports only blocks whose signatures verified,
    so the check is omitted rather than parameterized — no store
    invariant depends on which blocks are additionally rejected.
  - `prune_stale_attestation_data` is follow-up work; it enters as the
    `prune` parameter, constrained in the preservation theorem to leave
    the proof-relevant fields (blocks, states, checkpoints) unchanged —
    upstream it drops only vote-pool entries.

Proves FC-7 from `docs/lean4-proof-propositions.md`:
  - FC-7: `on_block` preserves the store invariants — `Store.WellFormed`
    together with the alignment clauses `Store.Aligned` that FC-6
    consumes (`onBlock_wellFormed`). The two residual hypotheses are
    the historical-chain alignment layer: the STF's advanced justified
    checkpoint names an imported block at its own slot, and it descends
    from the finalized checkpoint. Both are facts about
    `historical_block_hashes` mirroring the block map, a model layer
    this repository has not built yet (see the FC-7 catalog note).
-/

import LeanSpec.Forks.Lstar.Store.Ancestry

namespace LeanSpec.Forks.Lstar
namespace Store

/-! ## Alignment invariants (the FC-6 side conditions, now maintained) -/

/-- Store invariants beyond `WellFormed` that `on_block` maintains and
`update_head` consumes (FC-6's `hjslot` / `hdom` hypotheses, plus the
two state-alignment clauses their preservation runs on). -/
structure Aligned (st : Store) : Prop where
  /-- A stored post-state sits at its block's slot (the state is the
  result of transitioning to exactly that block). -/
  statesSlotAligned : ∀ r blk s₀, st.getBlock? r = some blk →
    st.getState? r = some s₀ → s₀.slot = blk.slot
  /-- Every stored post-state satisfies ST-4. -/
  statesJF : ∀ r s₀, st.getState? r = some s₀ →
    s₀.latestFinalized.slot ≤ s₀.latestJustified.slot
  /-- The justified checkpoint records the slot of its own block
  (FC-6's `hjslot`). -/
  justifiedSlotMatches : ∀ bj,
    st.getBlock? st.latestJustified.root = some bj →
    bj.slot = st.latestJustified.slot
  /-- No stored post-state finalizes past the store's justified slot
  (FC-6's `hdom`). -/
  statesDominated : ∀ r s₀, st.getState? r = some s₀ →
    s₀.latestFinalized.slot ≤ st.latestJustified.slot

/-- `Aligned` reads only blocks, states, and the justified checkpoint. -/
theorem aligned_congr {st st' : Store}
    (hb : st'.blocks = st.blocks) (hs : st'.states = st.states)
    (hj : st'.latestJustified = st.latestJustified)
    (hal : Aligned st) : Aligned st' := by
  have hgb : ∀ r, st'.getBlock? r = st.getBlock? r := by
    intro r; unfold getBlock?; rw [hb]
  have hgs : ∀ r, st'.getState? r = st.getState? r := by
    intro r; unfold getState?; rw [hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r blk s₀ h1 h2
    rw [hgb r] at h1
    rw [hgs r] at h2
    exact hal.statesSlotAligned r blk s₀ h1 h2
  · intro r s₀ h1
    rw [hgs r] at h1
    exact hal.statesJF r s₀ h1
  · intro bj h1
    rw [hj] at h1 ⊢
    rw [hgb] at h1
    exact hal.justifiedSlotMatches bj h1
  · intro r s₀ h1
    rw [hgs r] at h1
    rw [hj]
    exact hal.statesDominated r s₀ h1

/-- `WellFormed` reads only blocks, states, and the two checkpoints. -/
theorem wellFormed_congr {st st' : Store}
    (hb : st'.blocks = st.blocks) (hs : st'.states = st.states)
    (hj : st'.latestJustified = st.latestJustified)
    (hf : st'.latestFinalized = st.latestFinalized)
    (hwf : WellFormed st) : WellFormed st' := by
  have hgb : ∀ r, st'.getBlock? r = st.getBlock? r := by
    intro r; unfold getBlock?; rw [hb]
  have hgs : ∀ r, st'.getState? r = st.getState? r := by
    intro r; unfold getState?; rw [hs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb]; exact hwf.blocksKeysNodup
  · rw [hs]; exact hwf.statesKeysNodup
  · intro r; rw [hgb r, hgs r]; exact hwf.blocksStatesAligned r
  · intro p hp q hq heq
    rw [hb] at hp hq
    exact hwf.parentSlotLt p hp q hq heq
  · rw [hj, hgb]; exact hwf.justifiedInBlocks
  · rw [hj, hf, checkpointIsAncestor_congr hb]
    exact hwf.justifiedDescendsFromFinalized

/-! ## The import writes (`store.model_copy(update=...)`) -/

/-- Seed each block-carried vote into the known pool with an empty
proof set; existing entries win on collision
(`{data: set()} | store.latest_known_aggregated_payloads`). -/
def seedPayloads (atts : Array AggregatedAttestation)
    (pool : List (AttestationData × List SingleMessageAggregate)) :
    List (AttestationData × List SingleMessageAggregate) :=
  (((atts.toList.map (·.data)).eraseDups.filter
    (fun d => !(pool.any (fun p => p.1 == d)))).map
      (fun d => (d, ([] : List SingleMessageAggregate)))) ++ pool

/-- The store after `on_block`'s import writes, before the head update:
block and post-state stored under the block root, `latest_justified`
advanced from the post-state, block votes seeded. -/
def applyBlock (st : Store) (blockRoot : Root) (b : Block)
    (postState : State) : Store :=
  { st with
    blocks := (blockRoot, b) :: st.blocks
    states := (blockRoot, postState) :: st.states
    latestJustified := st.latestJustified.advanceTo postState.latestJustified
    latestKnownAggregatedPayloads :=
      seedPayloads b.body.attestations st.latestKnownAggregatedPayloads }

/-- Block lookup on the import store: the fresh root answers with the
new block, every other root answers as before. -/
theorem applyBlock_getBlock? (st : Store) (blockRoot : Root) (b : Block)
    (postState : State) (r : Root) :
    (applyBlock st blockRoot b postState).getBlock? r =
      if blockRoot == r then some b else st.getBlock? r := by
  unfold applyBlock getBlock?
  dsimp only
  cases h : blockRoot == r with
  | true => simp [h]
  | false => simp [h]

/-- State lookup on the import store, mirroring the block lookup. -/
theorem applyBlock_getState? (st : Store) (blockRoot : Root) (b : Block)
    (postState : State) (r : Root) :
    (applyBlock st blockRoot b postState).getState? r =
      if blockRoot == r then some postState else st.getState? r := by
  unfold applyBlock getState?
  dsimp only
  cases h : blockRoot == r with
  | true => simp [h]
  | false => simp [h]

/-- A stored state entry makes the state lookup succeed (the states-map
sibling of `getBlock?_isSome_of_mem`). -/
theorem getState?_isSome_of_mem {st : Store} {r : Root} {s₀ : State}
    (h : (r, s₀) ∈ st.states) : (st.getState? r).isSome := by
  unfold getState?
  cases hf : st.states.find? (fun q => q.1 == r) with
  | some _ => rfl
  | none =>
    have hnone := List.find?_eq_none.mp hf (r, s₀) h
    simp at hnone

/-! ## Walk stability under a fresh block -/

/-- The ancestor walk is stable under extending the block map: every
lookup the walk makes still answers the same. -/
theorem ancestorWalk_extend {st st' : Store}
    (hext : ∀ r bb, st.getBlock? r = some bb → st'.getBlock? r = some bb)
    (anc : Checkpoint) :
    ∀ (fuel : Nat) (r : Root), ancestorWalk st anc fuel r = true →
      ancestorWalk st' anc fuel r = true
  | 0, r, h => by simp [ancestorWalk] at h
  | fuel + 1, r, h => by
    unfold ancestorWalk at h ⊢
    cases hb : st.getBlock? r with
    | none =>
      rw [hb] at h
      simp at h
    | some bb =>
      rw [hb] at h
      rw [hext r bb hb]
      dsimp only at h ⊢
      split at h
      · next heq => rw [if_pos heq]; exact h
      · next hne =>
        rw [if_neg hne]
        split at h
        · simp at h
        · next hlt =>
          rw [if_neg hlt]
          exact ancestorWalk_extend hext anc fuel bb.parentRoot h

/-- A successful walk stays successful with more fuel: the walk reaches
its decision before the smaller fuel runs out. -/
theorem ancestorWalk_fuel_mono {st : Store} (anc : Checkpoint) :
    ∀ (fuel fuel' : Nat), fuel ≤ fuel' →
      ∀ (r : Root), ancestorWalk st anc fuel r = true →
        ancestorWalk st anc fuel' r = true
  | 0, _, _, r, h => by simp [ancestorWalk] at h
  | fuel + 1, 0, hle, _, _ => absurd hle (by omega)
  | fuel + 1, fuel' + 1, hle, r, h => by
    unfold ancestorWalk at h ⊢
    cases hb : st.getBlock? r with
    | none =>
      rw [hb] at h
      simp at h
    | some bb =>
      rw [hb] at h
      dsimp only at h ⊢
      split at h
      · next heq => rw [if_pos heq]; exact h
      · next hne =>
        rw [if_neg hne]
        split at h
        · simp at h
        · next hlt =>
          rw [if_neg hlt]
          exact ancestorWalk_fuel_mono anc fuel fuel' (by omega)
            bb.parentRoot h

/-- A stored ancestry clause survives the import: the fresh root never
shadows an existing lookup, and the one-longer block list only grants
the walk more fuel. -/
theorem checkpointIsAncestor_applyBlock {st : Store} {blockRoot : Root}
    {b : Block} {postState : State}
    (hfresh : st.getBlock? blockRoot = none) (anc desc : Checkpoint)
    (h : checkpointIsAncestor st anc desc = true) :
    checkpointIsAncestor (applyBlock st blockRoot b postState) anc desc
      = true := by
  unfold checkpointIsAncestor at h ⊢
  split at h
  · simp at h
  · next hg =>
    rw [if_neg hg]
    have hext : ∀ r bb, st.getBlock? r = some bb →
        (applyBlock st blockRoot b postState).getBlock? r = some bb := by
      intro r bb hr
      rw [applyBlock_getBlock?]
      by_cases hbr : (blockRoot == r) = true
      · exfalso
        rw [eq_of_beq hbr, hr] at hfresh
        cases hfresh
      · rw [if_neg hbr]; exact hr
    have hlen : (applyBlock st blockRoot b postState).blocks.length
        = st.blocks.length + 1 := rfl
    rw [hlen]
    exact ancestorWalk_fuel_mono anc (st.blocks.length + 1)
      (st.blocks.length + 1 + 1) (by omega) desc.root
      (ancestorWalk_extend hext anc _ _ h)

/-! ## `on_block` -/

/-- Process a new block and update the fork-choice state (`on_block`):
skip a known block, gate on the parent state and the #1182 horizon
bounds, reject duplicate vote data, run the state transition, write the
import, recompute the head, and prune stale votes when finalization
advanced past its snapshot. See the module docstring for the modeled
divergences (`blockRoot`, signatures, `prune`). -/
def onBlock [SSZ.HasHashTreeRoot AttestationData] (prune : Store → Store)
    (st : Store) (blockRoot : Root) (b : Block) : ST.Result Store :=
  if (st.getBlock? blockRoot).isSome then .ok st
  else
    match st.getState? b.parentRoot with
    | none => .error (.unknownParentBlock b.parentRoot)
    | some parentState =>
      if HISTORICAL_ROOTS_LIMIT < b.slot.toNat - parentState.slot.toNat then
        .error (.blockSlotGapTooLarge b.slot parentState.slot)
      else if st.time.toNat / INTERVALS_PER_SLOT + 1 < b.slot.toNat then
        .error (.blockTooFarInFuture b.slot
          (st.time.toNat / INTERVALS_PER_SLOT + 1))
      else if (b.body.attestations.toList.map (·.data)).eraseDups.length
          ≠ b.body.attestations.toList.length then
        .error .duplicateAttestationData
      else
        match State.transition parentState b with
        | .error e => .error e
        | .ok postState =>
          let st₂ := updateHead (applyBlock st blockRoot b postState)
          .ok (if st.latestFinalized.slot < st₂.latestFinalized.slot then
            prune st₂
          else st₂)


/-! ## FC-7: `on_block` preserves the store invariants -/

/-- The import writes preserve `WellFormed ∧ Aligned`: the fresh root
keeps the key sets distinct and aligned, the transition orders the new
parent link and refreshes the state alignment, and the advanced
justified checkpoint either is the old one (whose clauses transfer
across the grown block map) or is covered by the historical-chain
alignment hypothesis `hjcond`. -/
theorem applyBlock_invariants (st : Store) (blockRoot : Root) (b : Block)
    (parentState postState : State)
    (hwf : WellFormed st) (hal : Aligned st)
    (hfreshB : st.getBlock? blockRoot = none)
    (hfreshS : st.getState? blockRoot = none)
    (hparent : st.getState? b.parentRoot = some parentState)
    (htrans : State.transition parentState b = .ok postState)
    (hfreshParent : ∀ p ∈ st.blocks, p.2.parentRoot ≠ blockRoot)
    (hjcond : st.latestJustified.slot < postState.latestJustified.slot →
      (∃ bj, (applyBlock st blockRoot b postState).getBlock?
          postState.latestJustified.root = some bj ∧
        bj.slot = postState.latestJustified.slot) ∧
      checkpointIsAncestor (applyBlock st blockRoot b postState)
        st.latestFinalized postState.latestJustified = true) :
    WellFormed (applyBlock st blockRoot b postState) ∧
    Aligned (applyBlock st blockRoot b postState) := by
  have hparentNe : b.parentRoot ≠ blockRoot := by
    intro heq
    rw [heq, hfreshS] at hparent
    cases hparent
  have hslotLt : parentState.slot < b.slot :=
    State.transition_slot_lt _ _ _ htrans
  have hpostSlot : postState.slot = b.slot :=
    State.transition_state_slot _ _ _ htrans
  have hpostJF : postState.latestFinalized.slot ≤
      postState.latestJustified.slot :=
    State.transition_jf _ _ _ htrans
      (hal.statesJF b.parentRoot parentState hparent)
  have hgb := applyBlock_getBlock? st blockRoot b postState
  have hgs := applyBlock_getState? st blockRoot b postState
  have hjroot : st.latestJustified.root ≠ blockRoot := by
    intro heq
    have := hwf.justifiedInBlocks
    rw [heq, hfreshB] at this
    cases this
  -- The advanced justified checkpoint, by `advance_to`.
  have hadv : (applyBlock st blockRoot b postState).latestJustified =
      st.latestJustified.advanceTo postState.latestJustified := rfl
  have hadvCases :
      (applyBlock st blockRoot b postState).latestJustified
          = st.latestJustified ∨
      (st.latestJustified.slot < postState.latestJustified.slot ∧
        (applyBlock st blockRoot b postState).latestJustified
          = postState.latestJustified) := by
    rw [hadv]
    unfold Checkpoint.advanceTo
    by_cases hlt : st.latestJustified.slot < postState.latestJustified.slot
    · exact .inr ⟨hlt, if_pos hlt⟩
    · exact .inl (if_neg hlt)
  have hadvGeSelf : st.latestJustified.slot ≤
      (applyBlock st blockRoot b postState).latestJustified.slot := by
    rw [hadv]
    unfold Checkpoint.advanceTo
    by_cases hlt : st.latestJustified.slot < postState.latestJustified.slot
    · rw [if_pos hlt]
      exact UInt64.le_of_lt hlt
    · rw [if_neg hlt]
      exact UInt64.le_refl _
  have hadvGeCand : postState.latestJustified.slot ≤
      (applyBlock st blockRoot b postState).latestJustified.slot := by
    rw [hadv]
    unfold Checkpoint.advanceTo
    by_cases hlt : st.latestJustified.slot < postState.latestJustified.slot
    · rw [if_pos hlt]
      exact UInt64.le_refl _
    · rw [if_neg hlt]
      exact UInt64.not_lt.mp hlt
  constructor
  · -- `WellFormed` after the import.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Block keys stay distinct: the incoming root is new.
      show (((blockRoot, b) :: st.blocks).map (·.1)).Nodup
      rw [List.map_cons]
      refine List.nodup_cons.mpr ⟨?_, hwf.blocksKeysNodup⟩
      intro hmem
      obtain ⟨p, hp, hkey⟩ := List.mem_map.mp hmem
      have hpmem : (p.1, p.2) ∈ st.blocks := by simpa using hp
      have := getBlock?_isSome_of_mem hpmem
      rw [hkey, hfreshB] at this
      cases this
    · show (((blockRoot, postState) :: st.states).map (·.1)).Nodup
      rw [List.map_cons]
      refine List.nodup_cons.mpr ⟨?_, hwf.statesKeysNodup⟩
      intro hmem
      obtain ⟨p, hp, hkey⟩ := List.mem_map.mp hmem
      have hpmem : (p.1, p.2) ∈ st.states := by simpa using hp
      have := getState?_isSome_of_mem hpmem
      rw [hkey, hfreshS] at this
      cases this
    · intro r
      rw [hgb r, hgs r]
      by_cases hr : (blockRoot == r) = true
      · rw [if_pos hr, if_pos hr]
        exact ⟨fun _ => rfl, fun _ => rfl⟩
      · rw [if_neg hr, if_neg hr]
        exact hwf.blocksStatesAligned r
    · -- Parent-slot ordering over the four membership cases.
      intro p hp q hq heq
      have hp' : p ∈ (blockRoot, b) :: st.blocks := hp
      have hq' : q ∈ (blockRoot, b) :: st.blocks := hq
      cases List.mem_cons.mp hp' with
      | inl hpnew =>
        cases List.mem_cons.mp hq' with
        | inl hqnew =>
          exfalso
          rw [hpnew] at heq
          rw [hqnew] at heq
          exact hparentNe heq.symm
        | inr hqold =>
          -- New child over a stored parent: the parent block sits at
          -- the parent state's slot, below the block's slot.
          rw [hpnew]
          rw [hpnew] at heq
          have hqlook : st.getBlock? q.1 = some q.2 :=
            getBlock?_eq_some_of_mem hwf.blocksKeysNodup
              (by simpa using hqold)
          rw [heq] at hqlook
          have hslots := hal.statesSlotAligned b.parentRoot q.2
            parentState hqlook hparent
          show q.2.slot < b.slot
          rw [← hslots]
          exact hslotLt
      | inr hpold =>
        cases List.mem_cons.mp hq' with
        | inl hqnew =>
          exfalso
          rw [hqnew] at heq
          exact hfreshParent p (by simpa using hpold) heq.symm
        | inr hqold =>
          exact hwf.parentSlotLt p (by simpa using hpold) q
            (by simpa using hqold) heq
    · -- The justified anchor stays a known block.
      cases hadvCases with
      | inl heq =>
        rw [heq, hgb]
        by_cases hr : (blockRoot == st.latestJustified.root) = true
        · rw [if_pos hr]; rfl
        · rw [if_neg hr]; exact hwf.justifiedInBlocks
      | inr hc =>
        obtain ⟨⟨bj, hbj, _⟩, _⟩ := hjcond hc.1
        rw [hc.2, hbj]
        rfl
    · -- The justified chain still passes through finalized.
      have hfin : (applyBlock st blockRoot b postState).latestFinalized
          = st.latestFinalized := rfl
      cases hadvCases with
      | inl heq =>
        rw [heq, hfin]
        exact checkpointIsAncestor_applyBlock hfreshB st.latestFinalized
          st.latestJustified hwf.justifiedDescendsFromFinalized
      | inr hc =>
        obtain ⟨_, hdesc⟩ := hjcond hc.1
        rw [hc.2, hfin]
        exact hdesc
  · -- `Aligned` after the import.
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r blk s₀ h1 h2
      rw [hgb r] at h1
      rw [hgs r] at h2
      by_cases hr : (blockRoot == r) = true
      · rw [if_pos hr] at h1 h2
        injection h1 with h1'
        injection h2 with h2'
        rw [← h1', ← h2']
        exact hpostSlot
      · rw [if_neg hr] at h1 h2
        exact hal.statesSlotAligned r blk s₀ h1 h2
    · intro r s₀ h1
      rw [hgs r] at h1
      by_cases hr : (blockRoot == r) = true
      · rw [if_pos hr] at h1
        injection h1 with h1'
        rw [← h1']
        exact hpostJF
      · rw [if_neg hr] at h1
        exact hal.statesJF r s₀ h1
    · -- The advanced checkpoint still records its block's slot.
      cases hadvCases with
      | inl heq =>
        intro bj h1
        rw [heq] at h1 ⊢
        rw [hgb] at h1
        have hne : ¬((blockRoot == st.latestJustified.root) = true) := by
          intro hb'
          exact hjroot (eq_of_beq hb').symm
        rw [if_neg hne] at h1
        exact hal.justifiedSlotMatches bj h1
      | inr hc =>
        obtain ⟨⟨bj, hbj, hbjslot⟩, _⟩ := hjcond hc.1
        intro bj' h1
        rw [hc.2] at h1 ⊢
        rw [hbj] at h1
        injection h1 with h1'
        rw [← h1']
        exact hbjslot
    · intro r s₀ h1
      rw [hgs r] at h1
      by_cases hr : (blockRoot == r) = true
      · rw [if_pos hr] at h1
        injection h1 with h1'
        rw [← h1']
        exact UInt64.le_trans hpostJF hadvGeCand
      · rw [if_neg hr] at h1
        exact UInt64.le_trans (hal.statesDominated r s₀ h1) hadvGeSelf

/-- FC-7: a successful `on_block` preserves `WellFormed ∧ Aligned` —
the head-walk invariants together with the alignment clauses FC-6
consumes, so the composition `on_block → update_head` is closed.

Residual hypotheses, in upstream order of appearance:
  - `hprune` — pruning drops only vote-pool entries; the proof-relevant
    fields are untouched (upstream `prune_stale_attestation_data`).
  - `hfreshParent` — no already-stored block names the incoming root as
    its parent. Upstream this is STOR-1 plus hash acyclicity: a stored
    block's parent is stored or the anchor's dangling parent, the
    incoming root is new, and the anchor's parent can never pass the
    parent gate (its own parent sits below every stored block).
  - `hjnew` — when the state transition advances the justified
    checkpoint, the new checkpoint names an imported block at its own
    slot and descends from the finalized checkpoint. This is the
    historical-chain alignment layer (`historical_block_hashes`
    mirroring the block map), not yet modeled; see the catalog note. -/
theorem onBlock_wellFormed [SSZ.HasHashTreeRoot AttestationData]
    (prune : Store → Store)
    (hprune : ∀ s, (prune s).blocks = s.blocks ∧
      (prune s).states = s.states ∧
      (prune s).latestJustified = s.latestJustified ∧
      (prune s).latestFinalized = s.latestFinalized)
    (st st' : Store) (blockRoot : Root) (b : Block)
    (hwf : WellFormed st) (hal : Aligned st)
    (hfreshParent : ∀ p ∈ st.blocks, p.2.parentRoot ≠ blockRoot)
    (hjnew : ∀ parentState postState,
      st.getState? b.parentRoot = some parentState →
      State.transition parentState b = .ok postState →
      st.latestJustified.slot < postState.latestJustified.slot →
      (∃ bj, (applyBlock st blockRoot b postState).getBlock?
          postState.latestJustified.root = some bj ∧
        bj.slot = postState.latestJustified.slot) ∧
      checkpointIsAncestor (applyBlock st blockRoot b postState)
        st.latestFinalized postState.latestJustified = true)
    (h : onBlock prune st blockRoot b = .ok st') :
    WellFormed st' ∧ Aligned st' := by
  unfold onBlock at h
  split at h
  · -- Re-import of a known block: the store is returned unchanged.
    injection h with h'
    subst h'
    exact ⟨hwf, hal⟩
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
              obtain ⟨hwf₁, hal₁⟩ := applyBlock_invariants st blockRoot b
                parentState postState hwf hal hfreshB hfreshS hparent
                htrans hfreshParent
                (hjnew parentState postState hparent htrans)
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
              dsimp only at h
              injection h with h'
              subst h'
              split
              · obtain ⟨hpb, hps, hpj, hpf⟩ :=
                  hprune (updateHead (applyBlock st blockRoot b postState))
                exact ⟨wellFormed_congr hpb hps hpj hpf hwf₂,
                  aligned_congr hpb hps hpj hal₂⟩
              · exact ⟨hwf₂, hal₂⟩

end Store
end LeanSpec.Forks.Lstar
