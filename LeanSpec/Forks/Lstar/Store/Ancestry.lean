/-
Block ancestry and acyclicity of the fork-choice tree.

The parent-link relation on stored blocks, stated relationally: `a` is a
proper ancestor of `d` when following `parent_root` links from `d` one or
more steps inside the store lands on `a`. Upstream has no standalone
helper for this — the convention lives in the `_checkpoint_is_ancestor`
walk (`src/lean_spec/spec/forks/lstar/fork_choice.py`, modeled as
`Store.checkpointIsAncestor`) and in the parent-slot ordering established
at block insertion: `on_block` runs the state transition, which admits
only strictly-future block slots, so a stored child always sits strictly
above its stored parent (`Store.WellFormed.parentSlotLt`,
leanEthereum/leanSpec#1176 M-context).

Proves FC-4, FC-2, and FC-6 from `docs/lean4-proof-propositions.md`:
  - FC-4: the fork-choice tree is acyclic — on a well-formed store no
    stored block is a proper ancestor of itself (`fork_choice_acyclic`).
    Slots strictly decrease along every proper-ancestor step
    (`properAncestor_slot_lt`), so a cycle would need a slot strictly
    below itself.
  - FC-2: the head descends from the latest justified checkpoint
    (`head_descends_from_justified`): the GHOST walk starts at the
    justified root and only ever steps to stored children
    (`ghostWalk_ancestorOrEqual`), so the selected head is the anchor
    itself or a strict descendant (`computeLmdGhostHead_descends`).

The catalog samples decide ancestry with Boolean helpers
(`isProperAncestor`, `isAncestorOrEqual`); the relations are stated here
as `Prop`s instead — the walk that would decide them is exactly
`checkpointIsAncestor`'s, and the acyclicity/descent arguments need the
derivation structure, not the decision procedure.

Also proves FC-6: `update_head` preserves the store invariants
(`updateHead_wellFormed`) — only `head` and `latest_finalized` change,
and the re-derived finalized checkpoint stays on the justified chain;
see the FC-6 section docstring below for the argument and the two
`on_block`-maintained hypotheses.
-/

import LeanSpec.Forks.Lstar.Store.Store

namespace LeanSpec.Forks.Lstar
namespace Store

/-- `ProperAncestor st a d`: following `parent_root` links from `d` one
or more steps inside the store reaches `a`. The descendant of every step
must be stored; the ancestor end may name a root outside the store (a
genesis parent, e.g. the zero hash). -/
inductive ProperAncestor (st : Store) : Root → Root → Prop where
  /-- One step: `d` is stored and `a` is its parent link. -/
  | step {d : Root} {b : Block} (hd : st.getBlock? d = some b) :
      ProperAncestor st b.parentRoot d
  /-- Extend a derivation by one child step at the descendant end. -/
  | tail {a d : Root} {b : Block} (hd : st.getBlock? d = some b)
      (h : ProperAncestor st a b.parentRoot) :
      ProperAncestor st a d

/-- The descendant end of a proper-ancestor derivation is always a
stored block. -/
theorem ProperAncestor.descendant_block {st : Store} {a d : Root}
    (h : ProperAncestor st a d) : ∃ b, st.getBlock? d = some b := by
  cases h with
  | step hd => exact ⟨_, hd⟩
  | tail hd _ => exact ⟨_, hd⟩

/-- A stored entry makes the block lookup succeed (the existence half of
`getBlock?_eq_some_mem`). -/
theorem getBlock?_isSome_of_mem {st : Store} {r : Root} {b : Block}
    (h : (r, b) ∈ st.blocks) : (st.getBlock? r).isSome := by
  unfold getBlock?
  cases hf : st.blocks.find? (fun q => q.1 == r) with
  | some _ => rfl
  | none =>
    have hnone := List.find?_eq_none.mp hf (r, b) h
    simp at hnone

/-- Slots strictly decrease along proper ancestry on a well-formed
store: every step is a stored parent link, and
`WellFormed.parentSlotLt` orders each of them. -/
theorem properAncestor_slot_lt {st : Store} (hwf : WellFormed st)
    {a d : Root} (h : ProperAncestor st a d) :
    ∀ (ba bd : Block), st.getBlock? a = some ba →
      st.getBlock? d = some bd → ba.slot < bd.slot := by
  induction h with
  | @step d' b hd =>
    intro ba bd hba hbd
    have hb : b = bd := by rw [hd] at hbd; exact Option.some.inj hbd
    subst hb
    exact hwf.parentSlotLt (d', b) (getBlock?_eq_some_mem hd)
      (b.parentRoot, ba) (getBlock?_eq_some_mem hba) rfl
  | @tail a' d' b hd hpa ih =>
    intro ba bd hba hbd
    have hb : b = bd := by rw [hd] at hbd; exact Option.some.inj hbd
    subst hb
    obtain ⟨bp, hbp⟩ := hpa.descendant_block
    have h1 : ba.slot < bp.slot := ih ba bp hba hbp
    have h2 : bp.slot < b.slot :=
      hwf.parentSlotLt (d', b) (getBlock?_eq_some_mem hd)
        (b.parentRoot, bp) (getBlock?_eq_some_mem hbp) rfl
    have h1' := UInt64.lt_iff_toNat_lt.mp h1
    have h2' := UInt64.lt_iff_toNat_lt.mp h2
    exact UInt64.lt_iff_toNat_lt.mpr (by omega)

/-- FC-4: the fork-choice tree is acyclic — on a well-formed store no
stored block is a proper ancestor of itself. A cycle would put the
block's slot strictly below itself (`properAncestor_slot_lt`). -/
theorem fork_choice_acyclic (st : Store) (hwf : WellFormed st) :
    ∀ p ∈ st.blocks, ¬ ProperAncestor st p.1 p.1 := by
  intro p hp hcycle
  obtain ⟨bd, hbd⟩ :=
    Option.isSome_iff_exists.mp (getBlock?_isSome_of_mem hp)
  have hlt := properAncestor_slot_lt hwf hcycle bd bd hbd hbd
  have := UInt64.lt_iff_toNat_lt.mp hlt
  omega

/-! ## FC-2: the head descends from the latest justified checkpoint -/

/-- `a` is `d` itself or a proper ancestor of it (the catalog's
`isAncestorOrEqual`, stated relationally like `ProperAncestor`). -/
def AncestorOrEqual (st : Store) (a d : Root) : Prop :=
  a = d ∨ ProperAncestor st a d

/-- Proper ancestry composes: a derivation reaching `m` extends by the
derivation from `m` down to `d`. -/
theorem ProperAncestor.trans {st : Store} {a : Root} :
    ∀ {m d : Root}, ProperAncestor st a m → ProperAncestor st m d →
      ProperAncestor st a d
  | _, _, h1, .step hd => .tail hd h1
  | _, _, h1, .tail hd h => .tail hd (ProperAncestor.trans h1 h)

/-- With nodup keys (Python dict semantics), two stored entries sharing
a root are the same entry. -/
private theorem mem_unique_of_keys_nodup :
    ∀ {l : List (Root × Block)}, (l.map (·.1)).Nodup →
    ∀ {x y : Root × Block}, x ∈ l → y ∈ l → x.1 = y.1 → x = y
  | [], _, _, _, hx, _, _ => absurd hx (List.not_mem_nil)
  | p :: t, hnodup, x, y, hx, hy, hxy => by
    rw [List.map_cons] at hnodup
    have hnd := List.nodup_cons.mp hnodup
    cases List.mem_cons.mp hx with
    | inl hxp =>
      cases List.mem_cons.mp hy with
      | inl hyp => rw [hxp, hyp]
      | inr hyt =>
        exfalso
        apply hnd.1
        rw [hxp] at hxy
        rw [hxy]
        exact List.mem_map.mpr ⟨y, hyt, rfl⟩
    | inr hxt =>
      cases List.mem_cons.mp hy with
      | inl hyp =>
        exfalso
        apply hnd.1
        rw [hyp] at hxy
        rw [← hxy]
        exact List.mem_map.mpr ⟨x, hxt, rfl⟩
      | inr hyt => exact mem_unique_of_keys_nodup hnd.2 hxt hyt hxy

/-- With nodup keys, the lookup returns exactly the stored entry (the
uniqueness half of `getBlock?_eq_some_mem`). -/
theorem getBlock?_eq_some_of_mem {st : Store}
    (hnodup : (st.blocks.map (·.1)).Nodup) {r : Root} {b : Block}
    (h : (r, b) ∈ st.blocks) : st.getBlock? r = some b := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (getBlock?_isSome_of_mem h)
  have heq : ((r, v) : Root × Block) = (r, b) :=
    mem_unique_of_keys_nodup hnodup (getBlock?_eq_some_mem hv) h rfl
  rw [hv]
  rw [(Prod.mk.injEq ..).mp heq |>.2]

/-- An eligible child is stored with its parent link at `parent`
(strengthens `childrenOf_mem` under nodup keys). -/
theorem childrenOf_parent (st : Store) (weights : Weights)
    (minScore : Option Nat) (parent c : Root)
    (hnodup : (st.blocks.map (·.1)).Nodup)
    (h : c ∈ childrenOf st weights minScore parent) :
    ∃ b, st.getBlock? c = some b ∧ b.parentRoot = parent := by
  unfold childrenOf at h
  rw [List.mem_map] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hf := List.mem_filter.mp hp
  have hpar : p.2.parentRoot = parent :=
    eq_of_beq ((Bool.and_eq_true ..).mp hf.2).1
  exact ⟨p.2, getBlock?_eq_some_of_mem hnodup hf.1, hpar⟩

/-- The GHOST descent never leaves the subtree of its start: every step
moves to a stored child of the current head, so the start is an
ancestor-or-equal of the result. -/
theorem ghostWalk_ancestorOrEqual (st : Store) (weights : Weights)
    (minScore : Option Nat) (hnodup : (st.blocks.map (·.1)).Nodup) :
    ∀ (fuel : Nat) (head : Root),
      AncestorOrEqual st head (ghostWalk st weights minScore fuel head)
  | 0, _ => .inl rfl
  | fuel + 1, head => by
    cases hmc : maxChild weights (childrenOf st weights minScore head) with
    | none =>
      simp only [ghostWalk, hmc]
      exact .inl rfl
    | some best =>
      have hbmem := maxChild_mem weights _ best hmc
      obtain ⟨b, hgb, hparent⟩ :=
        childrenOf_parent st weights minScore head best hnodup hbmem
      have hstep : ProperAncestor st head best := by
        rw [← hparent]
        exact ProperAncestor.step hgb
      have ih := ghostWalk_ancestorOrEqual st weights minScore hnodup fuel best
      simp only [ghostWalk, hmc]
      cases ih with
      | inl heq => exact .inr (heq ▸ hstep)
      | inr hpa => exact .inr (hstep.trans hpa)

/-- The selected head sits in the subtree of the anchor it was asked to
start from — for any vote set and threshold, and regardless of whether
the anchor is stored (an unknown anchor is returned unchanged). -/
theorem computeLmdGhostHead_descends (st : Store)
    (hnodup : (st.blocks.map (·.1)).Nodup) (startRoot : Root)
    (attestations : List (Nat × AttestationData)) (minScore : Option Nat) :
    AncestorOrEqual st startRoot
      (computeLmdGhostHead st startRoot attestations minScore) := by
  unfold computeLmdGhostHead
  cases hb : st.getBlock? startRoot with
  | none => exact .inl rfl
  | some anchor =>
    exact ghostWalk_ancestorOrEqual st
      (accumulateAncestorWeights st attestations anchor.slot) minScore
      hnodup (st.blocks.length + 1) startRoot

/-- FC-2: the head descends from the latest justified checkpoint — the
GHOST walk starts at the justified root and only ever steps to stored
children, so `update_head` selects that root or a strict descendant. -/
theorem head_descends_from_justified [SSZ.HasHashTreeRoot AttestationData]
    (st : Store) (hwf : WellFormed st) :
    AncestorOrEqual st st.latestJustified.root (updateHead st).head := by
  have hhead : (updateHead st).head =
      computeLmdGhostHead st st.latestJustified.root
        (extractAttestationsFromAggregatedPayloads
          st.latestKnownAggregatedPayloads st.latestFinalized.slot) := rfl
  rw [hhead]
  exact computeLmdGhostHead_descends st hwf.blocksKeysNodup
    st.latestJustified.root
    (extractAttestationsFromAggregatedPayloads
      st.latestKnownAggregatedPayloads st.latestFinalized.slot) none

/-! ## FC-6: `update_head` preserves the store invariants

`updateHead` rewrites only `head` and `latestFinalized`, so five of the
six `WellFormed` clauses carry over untouched. The substantive one is
`justifiedDescendsFromFinalized`: the re-derived finalized checkpoint —
the head chain's ancestor at the head state's finalized slot — must
still sit on the justified checkpoint's chain. The argument: the head
descends from the justified root (FC-2), the re-derived root is an
ancestor of the head (`descendToSlot_ancestorOrEqual`), parent links
are unique so two ancestors of one block are comparable
(`properAncestor_comparable`), and the wrong order is killed by slots.
Completeness of the Boolean `ancestorWalk` against the relational
ancestry (`ancestorWalk_complete`) turns that into the stored clause;
its fuel argument counts distinct stored blocks below the walk's
position, which strictly shrinks every step. -/

/-- Parent links are unique, so two proper ancestors of one block are
comparable: one is an ancestor-or-equal of the other. -/
theorem properAncestor_comparable {st : Store} :
    ∀ {a j d : Root}, ProperAncestor st a d → ProperAncestor st j d →
      AncestorOrEqual st a j ∨ ProperAncestor st j a
  | _, _, _, @ProperAncestor.step _ _ b₁ hd₁,
      @ProperAncestor.step _ _ b₂ hd₂ => by
    have hb : b₂ = b₁ := Option.some.inj (hd₂.symm.trans hd₁)
    exact .inl (.inl (by rw [hb]))
  | _, _, _, @ProperAncestor.step _ _ b₁ hd₁,
      @ProperAncestor.tail _ _ _ b₂ hd₂ h₂ => by
    have hb : b₂ = b₁ := Option.some.inj (hd₂.symm.trans hd₁)
    exact .inr (hb ▸ h₂)
  | _, _, _, @ProperAncestor.tail _ _ _ b₁ hd₁ h₁,
      @ProperAncestor.step _ _ b₂ hd₂ => by
    have hb : b₂ = b₁ := Option.some.inj (hd₂.symm.trans hd₁)
    exact .inl (.inr (hb ▸ h₁))
  | _, _, _, @ProperAncestor.tail _ _ _ b₁ hd₁ h₁,
      @ProperAncestor.tail _ _ _ b₂ hd₂ h₂ => by
    have hb : b₂ = b₁ := Option.some.inj (hd₂.symm.trans hd₁)
    exact properAncestor_comparable h₁ (hb ▸ h₂)

/-- Comparability lifted to ancestor-or-equal: two ancestors of one
block sit on one chain. -/
theorem ancestors_comparable {st : Store} {a j d : Root}
    (ha : AncestorOrEqual st a d) (hj : AncestorOrEqual st j d) :
    AncestorOrEqual st a j ∨ ProperAncestor st j a := by
  cases ha with
  | inl heq =>
    cases hj with
    | inl heq' => exact .inl (.inl (heq.trans heq'.symm))
    | inr hpj => exact .inr (heq ▸ hpj)
  | inr hpa =>
    cases hj with
    | inl heq' => exact .inl (.inr (heq' ▸ hpa))
    | inr hpj => exact properAncestor_comparable hpa hpj

/-- The finalized re-derivation walk never leaves the ancestor chain of
its start: every step follows a stored parent link. -/
theorem descendToSlot_ancestorOrEqual (st : Store) (finalizedSlot : Slot) :
    ∀ (fuel : Nat) (r : Root),
      AncestorOrEqual st (descendToSlot st finalizedSlot fuel r) r
  | 0, r => .inl rfl
  | fuel + 1, r => by
    unfold descendToSlot
    cases hr : st.getBlock? r with
    | none => exact .inl rfl
    | some b =>
      dsimp only
      split
      · cases hp : st.getBlock? b.parentRoot with
        | none => exact .inl rfl
        | some bp =>
          dsimp only
          have hstep : ProperAncestor st b.parentRoot r :=
            ProperAncestor.step hr
          have ih :=
            descendToSlot_ancestorOrEqual st finalizedSlot fuel b.parentRoot
          cases ih with
          | inl heq => exact .inr (by rw [heq]; exact hstep)
          | inr hpa => exact .inr (hpa.trans hstep)
      · exact .inl rfl

/-- Dropping entries can only shorten a filter. -/
private theorem filter_length_mono {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl _
  | x :: t, himp => by
    have ht := filter_length_mono p q t
      (fun y hy => himp y (List.mem_cons_of_mem x hy))
    cases hp : p x with
    | true =>
      rw [List.filter_cons_of_pos hp,
        List.filter_cons_of_pos (himp x List.mem_cons_self hp)]
      exact Nat.succ_le_succ ht
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp])]
      cases hq : q x with
      | true =>
        rw [List.filter_cons_of_pos hq]
        exact Nat.le_succ_of_le ht
      | false =>
        rw [List.filter_cons_of_neg (by simp [hq])]
        exact ht

/-- A member kept by `q` but dropped by `p` makes the `p`-filter
strictly shorter. -/
private theorem filter_length_lt {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
      ∀ w ∈ l, q w = true → p w = false →
      (l.filter p).length < (l.filter q).length
  | [], _, w, hw, _, _ => absurd hw (List.not_mem_nil)
  | x :: t, himp, w, hw, hqw, hpw => by
    have himpt : ∀ y ∈ t, p y = true → q y = true :=
      fun y hy => himp y (List.mem_cons_of_mem x hy)
    cases List.mem_cons.mp hw with
    | inl hwx =>
      subst hwx
      rw [List.filter_cons_of_neg (by simp [hpw]),
        List.filter_cons_of_pos hqw]
      exact Nat.lt_succ_of_le (filter_length_mono p q t himpt)
    | inr hwt =>
      have ht := filter_length_lt p q t himpt w hwt hqw hpw
      cases hp : p x with
      | true =>
        rw [List.filter_cons_of_pos hp,
          List.filter_cons_of_pos (himp x List.mem_cons_self hp)]
        exact Nat.succ_lt_succ ht
      | false =>
        rw [List.filter_cons_of_neg (by simp [hp])]
        cases hq : q x with
        | true =>
          rw [List.filter_cons_of_pos hq]
          exact Nat.lt_succ_of_lt ht
        | false =>
          rw [List.filter_cons_of_neg (by simp [hq])]
          exact ht

/-- Stored entries at or below a slot — the fuel measure of
`ancestorWalk_complete`. Every walk step strictly shrinks it: the
current block leaves the count and parent steps strictly lower the
slot. -/
private def slotCount (st : Store) (s : Slot) : Nat :=
  (st.blocks.filter (fun p => decide (p.2.slot.toNat ≤ s.toNat))).length

private theorem slotCount_le (st : Store) (s : Slot) :
    slotCount st s ≤ st.blocks.length :=
  List.length_filter_le _ _

/-- A parent step strictly shrinks the measure: the child's entry
counts for the child's slot but not for the strictly lower parent
slot. -/
private theorem slotCount_lt {st : Store} {d : Root} {bd : Block}
    (hd : st.getBlock? d = some bd) {s : Slot}
    (hlt : s.toNat < bd.slot.toNat) :
    slotCount st s < slotCount st bd.slot := by
  apply filter_length_lt _ _ st.blocks
  · intro x _ hx
    have h1 := of_decide_eq_true hx
    exact decide_eq_true (Nat.le_trans h1 (Nat.le_of_lt hlt))
  · exact getBlock?_eq_some_mem hd
  · exact decide_eq_true (Nat.le_refl _)
  · exact decide_eq_false (show ¬(bd.slot.toNat ≤ s.toNat) by omega)

/-- Completeness of the `_checkpoint_is_ancestor` walk against the
relational ancestry: starting anywhere on a chain that contains the
ancestor — whose stored block sits exactly at the checkpoint's slot —
the walk finds it, given fuel for the stored blocks at or below the
start. Slots strictly decrease along the chain, so the walk can neither
stop early at the ancestor's slot on a different root nor jump past
it. -/
theorem ancestorWalk_complete {st : Store} (hwf : WellFormed st)
    (anc : Checkpoint) {ar : Root} (har : anc.root = ar) {ba : Block}
    (hba : st.getBlock? ar = some ba) (hslot : ba.slot = anc.slot) :
    ∀ (fuel : Nat) (d : Root) (bd : Block),
      st.getBlock? d = some bd →
      AncestorOrEqual st ar d →
      slotCount st bd.slot ≤ fuel →
      ancestorWalk st anc fuel d = true
  | 0, d, bd, hbd, _, hfuel => by
    exfalso
    have hmem : (d, bd) ∈ st.blocks := getBlock?_eq_some_mem hbd
    have : 0 < slotCount st bd.slot := by
      apply List.length_pos_of_mem
      exact List.mem_filter.mpr ⟨hmem, decide_eq_true (Nat.le_refl _)⟩
    omega
  | fuel + 1, d, bd, hbd, hanc, hfuel => by
    unfold ancestorWalk
    rw [hbd]
    dsimp only
    by_cases hslots : bd.slot = anc.slot
    · rw [if_pos hslots]
      -- At the ancestor's slot the chain position is the ancestor
      -- itself: a proper ancestor would sit strictly below.
      cases hanc with
      | inl heq =>
        rw [← heq, har]
        exact beq_self_eq_true ar
      | inr hpa =>
        exfalso
        have hlt := properAncestor_slot_lt hwf hpa ba bd hba hbd
        have h1 := UInt64.lt_iff_toNat_lt.mp hlt
        have h2 : ba.slot = bd.slot := by rw [hslot, hslots]
        rw [h2] at h1
        omega
    · rw [if_neg hslots]
      by_cases hbelow : bd.slot < anc.slot
      · exfalso
        -- The chain cannot start below the ancestor it contains.
        cases hanc with
        | inl heq =>
          rw [heq] at hba
          have : ba = bd := Option.some.inj (hba.symm.trans hbd)
          rw [this] at hslot
          exact hslots hslot
        | inr hpa =>
          have hlt := properAncestor_slot_lt hwf hpa ba bd hba hbd
          have h1 := UInt64.lt_iff_toNat_lt.mp hlt
          have h2 := UInt64.lt_iff_toNat_lt.mp hbelow
          have h3 : ba.slot.toNat = anc.slot.toNat := by rw [hslot]
          omega
      · rw [if_neg hbelow]
        -- Strictly above the ancestor: the position cannot be the
        -- ancestor itself, so the derivation steps to the parent.
        have hne : ar ≠ d := by
          intro heq
          rw [heq] at hba
          have : ba = bd := Option.some.inj (hba.symm.trans hbd)
          rw [this] at hslot
          exact hslots hslot
        cases hanc with
        | inl heq => exact absurd heq hne
        | inr hpa =>
          cases hpa with
          | @step _ b' hd' =>
            -- The ancestor is the parent link itself.
            have hb' : bd = b' := Option.some.inj (hbd.symm.trans hd')
            subst hb'
            have hplt : ba.slot < bd.slot :=
              hwf.parentSlotLt (d, bd) (getBlock?_eq_some_mem hbd)
                (bd.parentRoot, ba) (getBlock?_eq_some_mem hba) rfl
            exact ancestorWalk_complete hwf anc har hba hslot fuel
              bd.parentRoot ba hba (.inl rfl)
              (by
                have := slotCount_lt hbd (UInt64.lt_iff_toNat_lt.mp hplt)
                omega)
          | @tail _ _ b' hd' hpa' =>
            have hb' : bd = b' := Option.some.inj (hbd.symm.trans hd')
            subst hb'
            obtain ⟨bp, hbp⟩ := hpa'.descendant_block
            have hplt : bp.slot < bd.slot :=
              hwf.parentSlotLt (d, bd) (getBlock?_eq_some_mem hbd)
                (bd.parentRoot, bp) (getBlock?_eq_some_mem hbp) rfl
            exact ancestorWalk_complete hwf anc har hba hslot fuel
              bd.parentRoot bp hbp (.inr hpa')
              (by
                have := slotCount_lt hbd (UInt64.lt_iff_toNat_lt.mp hplt)
                omega)

/-- The stored `checkpointIsAncestor` clause from relational ancestry:
an ancestor whose block sits exactly at its slot, on the chain of a
descendant checkpoint no earlier than it, is found by the walk. -/
theorem checkpointIsAncestor_of_ancestorOrEqual {st : Store}
    (hwf : WellFormed st) (anc desc : Checkpoint) {ba bd : Block}
    (hba : st.getBlock? anc.root = some ba) (hslot : ba.slot = anc.slot)
    (hbd : st.getBlock? desc.root = some bd)
    (hanc : AncestorOrEqual st anc.root desc.root)
    (hle : anc.slot ≤ desc.slot) :
    checkpointIsAncestor st anc desc = true := by
  unfold checkpointIsAncestor
  rw [if_neg (UInt64.not_lt.mpr hle)]
  exact ancestorWalk_complete hwf anc rfl hba hslot (st.blocks.length + 1)
    desc.root bd hbd hanc
    (Nat.le_trans (slotCount_le st bd.slot) (Nat.le_succ _))

/-- `checkpointIsAncestor` reads only the block map, which `updateHead`
never touches. -/
private theorem ancestorWalk_congr {st st' : Store}
    (hblocks : st'.blocks = st.blocks) (anc : Checkpoint) :
    ∀ (fuel : Nat) (r : Root),
      ancestorWalk st' anc fuel r = ancestorWalk st anc fuel r
  | 0, _ => rfl
  | fuel + 1, r => by
    unfold ancestorWalk
    have hget : st'.getBlock? r = st.getBlock? r := by
      unfold getBlock?
      rw [hblocks]
    rw [hget]
    cases st.getBlock? r with
    | none => rfl
    | some b =>
      dsimp only
      split
      · rfl
      · split
        · rfl
        · exact ancestorWalk_congr hblocks anc fuel b.parentRoot

private theorem checkpointIsAncestor_congr {st st' : Store}
    (hblocks : st'.blocks = st.blocks) (anc desc : Checkpoint) :
    checkpointIsAncestor st' anc desc = checkpointIsAncestor st anc desc := by
  unfold checkpointIsAncestor
  rw [hblocks, ancestorWalk_congr hblocks]

/-- FC-6: `update_head` preserves the store invariants. Only `head` and
`latestFinalized` change, so the block/state clauses carry over; the
re-derived finalized checkpoint stays on the justified chain because it
is the head chain's ancestor at the head state's finalized slot, the
head descends from the justified root (FC-2), and one chain orders its
ancestors by slot.

The two extra hypotheses are store invariants upstream's `on_block`
maintains outside `update_head`'s reach, stated explicitly rather than
grown into `WellFormed`:
  - `hjslot` — the justified checkpoint records the slot of its own
    block (`validate_attestation` enforces exactly this shape for every
    vote checkpoint; `on_block` builds `latest_justified` from
    checkpoints produced by the STF, which pairs each root with its
    block's slot).
  - `hdom` — no stored post-state finalizes past the store's justified
    slot (`on_block` advances `store.latest_justified` over every
    stored state's justified checkpoint, and ST-4 bounds each state's
    finalized slot by its justified slot). -/
theorem updateHead_wellFormed [SSZ.HasHashTreeRoot AttestationData]
    (st : Store) (hwf : WellFormed st)
    (hjslot : ∀ bj, st.getBlock? st.latestJustified.root = some bj →
      bj.slot = st.latestJustified.slot)
    (hdom : ∀ r s₀, st.getState? r = some s₀ →
      s₀.latestFinalized.slot ≤ st.latestJustified.slot) :
    WellFormed (updateHead st) := by
  have hblocks : (updateHead st).blocks = st.blocks := rfl
  have hjust : (updateHead st).latestJustified = st.latestJustified := rfl
  refine ⟨hwf.blocksKeysNodup, hwf.statesKeysNodup,
    hwf.blocksStatesAligned, hwf.parentSlotLt, hwf.justifiedInBlocks, ?_⟩
  rw [checkpointIsAncestor_congr hblocks, hjust]
  -- The new finalized checkpoint, by the cases of `update_head`'s
  -- re-derivation.
  show checkpointIsAncestor st
    (match st.getState?
        (computeLmdGhostHead st st.latestJustified.root
          (extractAttestationsFromAggregatedPayloads
            st.latestKnownAggregatedPayloads st.latestFinalized.slot)) with
      | none => st.latestFinalized
      | some headState =>
        let finalizedSlot := headState.latestFinalized.slot
        let finalizedRoot :=
          descendToSlot st finalizedSlot (st.blocks.length + 1)
            (computeLmdGhostHead st st.latestJustified.root
              (extractAttestationsFromAggregatedPayloads
                st.latestKnownAggregatedPayloads st.latestFinalized.slot))
        match st.getBlock? finalizedRoot with
        | none => st.latestFinalized
        | some b =>
          if b.slot = finalizedSlot then
            { root := finalizedRoot, slot := finalizedSlot }
          else st.latestFinalized)
    st.latestJustified = true
  cases hstate : st.getState?
      (computeLmdGhostHead st st.latestJustified.root
        (extractAttestationsFromAggregatedPayloads
          st.latestKnownAggregatedPayloads st.latestFinalized.slot)) with
  | none => exact hwf.justifiedDescendsFromFinalized
  | some headState =>
    dsimp only
    cases hfb : st.getBlock?
        (descendToSlot st headState.latestFinalized.slot
          (st.blocks.length + 1)
          (computeLmdGhostHead st st.latestJustified.root
            (extractAttestationsFromAggregatedPayloads
              st.latestKnownAggregatedPayloads st.latestFinalized.slot))) with
    | none => exact hwf.justifiedDescendsFromFinalized
    | some b =>
      dsimp only
      by_cases hbslot : b.slot = headState.latestFinalized.slot
      · rw [if_pos hbslot]
        -- The substantive case: the re-derived checkpoint.
        obtain ⟨bj, hbj⟩ :=
          Option.isSome_iff_exists.mp hwf.justifiedInBlocks
        have hbjslot := hjslot bj hbj
        have hfslot := hdom _ _ hstate
        -- The head descends from the justified root; the re-derived
        -- root is an ancestor of the head.
        have hhead := computeLmdGhostHead_descends st hwf.blocksKeysNodup
          st.latestJustified.root
          (extractAttestationsFromAggregatedPayloads
            st.latestKnownAggregatedPayloads st.latestFinalized.slot) none
        have hdesc := descendToSlot_ancestorOrEqual st
          headState.latestFinalized.slot (st.blocks.length + 1)
          (computeLmdGhostHead st st.latestJustified.root
            (extractAttestationsFromAggregatedPayloads
              st.latestKnownAggregatedPayloads st.latestFinalized.slot))
        -- Two ancestors of the head are comparable; the justified root
        -- below the re-derived one would order the slots backwards.
        cases ancestors_comparable hdesc hhead with
        | inl hanc =>
          exact checkpointIsAncestor_of_ancestorOrEqual hwf _ _ hfb hbslot
            hbj hanc hfslot
        | inr hpj =>
          exfalso
          have hlt := properAncestor_slot_lt hwf hpj bj b hbj hfb
          have h1 := UInt64.lt_iff_toNat_lt.mp hlt
          have h2 := UInt64.le_iff_toNat_le.mp hfslot
          have h3 : bj.slot.toNat = st.latestJustified.slot.toNat := by
            rw [hbjslot]
          have h4 : b.slot.toNat = headState.latestFinalized.slot.toNat := by
            rw [hbslot]
          omega
      · rw [if_neg hbslot]
        exact hwf.justifiedDescendsFromFinalized

end Store
end LeanSpec.Forks.Lstar
