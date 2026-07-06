/-
Block-store chain structure: every stored block's parent is stored.

The catalog sources STOR-1 to a `Database.add_block` parent-existence
precondition; in current leanSpec no such database method exists — the
gate lives in fork choice: `on_block`
(`src/lean_spec/spec/forks/lstar/fork_choice.py`) rejects a block whose
parent state is not in the store (`UNKNOWN_PARENT_BLOCK`) before
`SyncService._persist_block` writes anything, so a block reaches the
block map only when its parent is already there. The exception is the
chain anchor: `create_store` seeds the map with a block whose parent is
outside the tree — the zero hash for a genesis anchor, an absent block
for a checkpoint-sync anchor.

Modeled here as the guarded insertion `insertBlock` (the parent gate of
`on_block`, with the upstream `dict` replace-by-key) on the fork-choice
`Store`, and the invariant `ParentsPresent` it maintains.

Proves STOR-1 from `docs/lean4-proof-propositions.md`:
  - STOR-1: every non-anchor block has its parent in the store —
    anchoring establishes the invariant (`parentsPresent_anchor`),
    guarded insertion preserves it (`parentsPresent_insertBlock`), and
    on a genesis-anchored store it takes the catalog's form: a stored
    block's parent is the zero hash or itself stored
    (`parent_exists_or_genesis`).
-/

import LeanSpec.Forks.Lstar.Store.Ancestry

namespace LeanSpec.Storage

open LeanSpec.Forks.Lstar
open LeanSpec.Forks.Lstar.Store (getBlock?_eq_some_of_mem)

namespace Store

open LeanSpec.Forks.Lstar.Store

/-- Insert a block under its root, gated on the parent being known —
the `UNKNOWN_PARENT_BLOCK` rejection of `on_block`, at the point where
the block enters the store's block map (upstream `dict` assignment,
replacing any entry with the same root). -/
def insertBlock (st : LeanSpec.Forks.Lstar.Store) (root : Root)
    (b : Block) : ST.Result LeanSpec.Forks.Lstar.Store :=
  if (st.getBlock? b.parentRoot).isSome then
    .ok { st with
      blocks := (root, b) :: st.blocks.filter (fun p => !(p.1 == root)) }
  else
    .error (.unknownParentBlock b.parentRoot)

/-- STOR-1 invariant: every stored block is the chain anchor or has its
parent stored (the anchor's parent is outside the tree — the zero hash
for genesis, an absent block for a checkpoint-sync anchor). -/
def ParentsPresent (st : LeanSpec.Forks.Lstar.Store)
    (anchorRoot : Root) : Prop :=
  ∀ p ∈ st.blocks,
    p.1 = anchorRoot ∨ (st.getBlock? p.2.parentRoot).isSome

/-- A freshly anchored store satisfies the invariant (`create_store`
seeds `blocks` with exactly the anchor). -/
theorem parentsPresent_anchor (st : LeanSpec.Forks.Lstar.Store)
    (anchorRoot : Root) (anchorBlock : Block)
    (hblocks : st.blocks = [(anchorRoot, anchorBlock)]) :
    ParentsPresent st anchorRoot := by
  intro p hp
  rw [hblocks] at hp
  cases hp with
  | head => exact .inl rfl
  | tail _ h => cases h

/-- A successful lookup survives a replace-by-key insertion: the new
entry answers for its own root, and every other root still finds its
old entry behind the filter. -/
private theorem getBlock?_isSome_insert
    (st : LeanSpec.Forks.Lstar.Store) (root : Root) (b : Block) (k : Root)
    (h : (st.getBlock? k).isSome) :
    ((List.find? (fun p => p.1 == k)
      ((root, b) :: st.blocks.filter (fun p => !(p.1 == root)))).map
        (·.2)).isSome := by
  by_cases hk : (root == k) = true
  · simp [List.find?, hk]
  · rw [List.find?]
    simp only [hk]
    unfold LeanSpec.Forks.Lstar.Store.getBlock? at h
    have hroot : k ≠ root := fun hc => hk (hc ▸ beq_self_eq_true root)
    -- The old entry for `k` survives the filter, so `find?` still
    -- succeeds; induct over the block list.
    have : ∀ (l : List (Root × Block)),
        ((l.find? (fun p => p.1 == k)).map (·.2)).isSome →
        (((l.filter (fun p => !(p.1 == root))).find?
          (fun p => p.1 == k)).map (·.2)).isSome := by
      intro l
      induction l with
      | nil => intro hf; simp [List.find?] at hf
      | cons e t ih =>
        intro hf
        by_cases hek : (e.1 == k) = true
        · have hene : (e.1 == root) = false := by
            have : e.1 = k := eq_of_beq hek
            subst this
            exact beq_eq_false_iff_ne.mpr hroot
          rw [List.filter_cons_of_pos (by simp [hene])]
          simp [List.find?, hek]
        · rw [List.find?] at hf
          simp only [hek] at hf
          by_cases her : (e.1 == root) = true
          · rw [List.filter_cons_of_neg (by simp [her])]
            exact ih hf
          · rw [List.filter_cons_of_pos (by simp [her])]
            rw [List.find?]
            simp only [hek]
            exact ih hf
    exact this st.blocks h

/-- STOR-1, preservation: the parent-gated insertion keeps every stored
block's parent stored — the new block's parent was required present,
and a replace-by-key insertion never makes a present root absent. -/
theorem parentsPresent_insertBlock
    (st st' : LeanSpec.Forks.Lstar.Store) (anchorRoot root : Root)
    (b : Block)
    (hpp : ParentsPresent st anchorRoot)
    (h : insertBlock st root b = .ok st') :
    ParentsPresent st' anchorRoot := by
  unfold insertBlock at h
  split at h
  · next hparent =>
    injection h with h'
    subst h'
    intro p hp
    cases List.mem_cons.mp hp with
    | inl hnew =>
      subst hnew
      exact .inr (getBlock?_isSome_insert st root b _ hparent)
    | inr hold =>
      have hmem := (List.mem_filter.mp hold).1
      cases hpp p hmem with
      | inl hanchor => exact .inl hanchor
      | inr hpresent =>
        exact .inr (getBlock?_isSome_insert st root b _ hpresent)
  · simp at h

/-- STOR-1, catalog form: on a genesis-anchored store — the invariant
plus an anchor whose block carries the zero-hash parent — every stored
block's parent is the zero hash or itself stored. -/
theorem parent_exists_or_genesis (st : LeanSpec.Forks.Lstar.Store)
    (anchorRoot : Root)
    (hpp : ParentsPresent st anchorRoot)
    (hanchor : ∀ p ∈ st.blocks,
      p.1 = anchorRoot → p.2.parentRoot = SSZ.Bytes32.zero) :
    ∀ p ∈ st.blocks,
      p.2.parentRoot = SSZ.Bytes32.zero ∨
      (st.getBlock? p.2.parentRoot).isSome := by
  intro p hp
  cases hpp p hp with
  | inl hroot => exact .inl (hanchor p hp hroot)
  | inr hpresent => exact .inr hpresent

end Store
end LeanSpec.Storage
