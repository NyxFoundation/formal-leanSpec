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

Proves FC-4 and FC-2 from `docs/lean4-proof-propositions.md`:
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

end Store
end LeanSpec.Forks.Lstar
