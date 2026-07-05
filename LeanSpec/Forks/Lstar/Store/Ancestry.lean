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

Proves FC-4 from `docs/lean4-proof-propositions.md`:
  - FC-4: the fork-choice tree is acyclic — on a well-formed store no
    stored block is a proper ancestor of itself (`fork_choice_acyclic`).
    Slots strictly decrease along every proper-ancestor step
    (`properAncestor_slot_lt`), so a cycle would need a slot strictly
    below itself.

The catalog sample decides ancestry with a Boolean `isProperAncestor`;
the relation is stated here as an inductive `Prop` instead — the walk
that would decide it is exactly `checkpointIsAncestor`'s, and the
acyclicity argument needs the derivation structure, not the decision
procedure.
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

end Store
end LeanSpec.Forks.Lstar
