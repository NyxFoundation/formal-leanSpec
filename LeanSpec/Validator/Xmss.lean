/-
XMSS key-preparation state management (the validator-side call site).

Mirrors the preparation-window bookkeeping of
`src/lean_spec/spec/crypto/xmss/containers.py` (`SecretKey`) and
`src/lean_spec/spec/crypto/xmss/interface.py`
(`GeneralizedXmssScheme.get_prepared_interval` / `advance_preparation`):
  - the signer keeps two adjacent bottom trees resident; with
    `W = LEAVES_PER_BOTTOM_TREE`, tree `i` covers slots `[i·W, (i+1)·W)`
    and the prepared window covers `[i·W, (i+2)·W)`.
  - `advance_preparation` slides the window one bottom tree forward:
    nothing happens once the next window would exceed the activation
    interval ("returning the same key when no advancement is possible
    keeps callers simple"); otherwise the right tree rotates into the
    left slot, a fresh right tree is rebuilt from the PRF key, and the
    index advances by one.

Cryptography stays on the Arklib side, per the catalog's out-of-scope
notice — VAL-5 covers only this state management. Concretely:
  - `HashSubTree`, the PRF key, and the public parameter are opaque
    payloads, and the Phase-2 tree regeneration
    (`HashSubTree.from_prf_key`) enters as the `rebuild` parameter — the
    window arithmetic is independent of tree contents, so the theorems
    hold for every regenerator.
  - Python's `Uint64` constructor raises when the successor index would
    leave the type; the model folds that edge into "no advancement
    possible" (the key is returned unchanged), keeping the operation
    total. Real activation windows sit far below the boundary.

The signing path (`ValidatorService._sign_with_key`) loops
`advance_preparation` until the duty slot enters the prepared window —
the monotonicity proved here is what moves that loop forward.

Proves VAL-5 from `docs/lean4-proof-propositions.md`:
  - VAL-5: the XMSS preparation state is monotonically increasing —
    unconditionally the prepared window never rewinds
    (`advancePreparation_monotone`), and it advances strictly while the
    activation interval still has room
    (`advancePreparation_strict_mono`, the catalog statement with its
    true precondition); past the interval the key is a fixed point
    (`advancePreparation_exhausted`).
-/

import LeanSpec.Aliases

namespace LeanSpec.Validator.Xmss

/-- Opaque stand-in for an XMSS `HashSubTree` (top or bottom tree).
Internal structure and hashing are Arklib-side; only the serialized
payload is carried, as with `MultiMessageAggregate`. -/
structure HashSubTree where
  payload : ByteArray
  deriving Inhabited

/-- Private state of an XMSS key pair (`SecretKey`) — the
preparation-relevant view: the PRF seed and trees are opaque, the
window bookkeeping fields are exact. -/
structure SecretKey where
  /-- Master secret seed; every one-time key derives from it (opaque). -/
  prfKey : ByteArray
  /-- Public parameter mirrored so signing is self-contained (opaque). -/
  parameter : ByteArray
  /-- First slot this key can sign for. -/
  activationSlot : Slot
  /-- Number of consecutive slots this key can sign for. -/
  numActiveSlots : SSZ.Uint64
  /-- Full top tree, always resident (opaque). -/
  topTree : HashSubTree
  /-- Bottom-tree index `i` for the left half of the prepared window. -/
  leftBottomTreeIndex : SSZ.Uint64
  /-- Bottom tree at index `i`, covering slots `[i·W, (i+1)·W)` (opaque). -/
  leftBottomTree : HashSubTree
  /-- Bottom tree at index `i+1`, covering `[(i+1)·W, (i+2)·W)` (opaque). -/
  rightBottomTree : HashSubTree
  deriving Inhabited

/-- The configuration slice the preparation window depends on
(`GeneralizedXmssScheme.config.LEAVES_PER_BOTTOM_TREE`; a power of two
upstream, hence positive). -/
structure Scheme where
  leavesPerBottomTree : Nat
  deriving Inhabited, Repr

namespace Scheme

/-- First slot of the prepared interval (`get_prepared_interval`'s
`start = i · W`). -/
def preparedStart (s : Scheme) (sk : SecretKey) : Nat :=
  sk.leftBottomTreeIndex.toNat * s.leavesPerBottomTree

/-- One-past-the-last slot of the prepared interval
(`range(start, start + 2·W)`): the window covered by the two resident
bottom trees. -/
def preparedEnd (s : Scheme) (sk : SecretKey) : Nat :=
  (sk.leftBottomTreeIndex.toNat + 2) * s.leavesPerBottomTree

/-- One-past-the-last slot the key may sign for
(`activation_slot + num_active_slots`, in exact integers as Python). -/
def activationEnd (sk : SecretKey) : Nat :=
  sk.activationSlot.toNat + sk.numActiveSlots.toNat

/-- Slide the prepared window one bottom tree forward
(`advance_preparation`). Phase 1 bails out unchanged when the next
window would exceed the activation interval — or, in the model, when
the successor index would leave `Uint64` (Python's constructor raises
there; see the module docstring). Phase 2's tree regeneration is the
`rebuild` parameter; Phase 3 rotates the right tree into the left slot
and advances the index. -/
def advancePreparation (s : Scheme) (rebuild : SSZ.Uint64 → HashSubTree)
    (sk : SecretKey) : SecretKey :=
  let i := sk.leftBottomTreeIndex.toNat
  -- Phase 1: no advancement once the activation interval is consumed.
  if activationEnd sk < (i + 3) * s.leavesPerBottomTree then sk
  -- Model guard: the successor indices must stay representable.
  else if 2 ^ 64 ≤ i + 2 then sk
  else
    -- Phase 3 (Phase 2 is `rebuild`): rotate and advance.
    { sk with
      leftBottomTree := sk.rightBottomTree
      rightBottomTree := rebuild (UInt64.ofNat (i + 2))
      leftBottomTreeIndex := UInt64.ofNat (i + 1) }

/-- VAL-5, unconditional half: the prepared window never rewinds — the
slashing-safety core (a rewound window would re-expose consumed
one-time keys). Holds for every regenerator and every configuration. -/
theorem advancePreparation_monotone (s : Scheme)
    (rebuild : SSZ.Uint64 → HashSubTree) (sk : SecretKey) :
    preparedEnd s sk ≤ preparedEnd s (advancePreparation s rebuild sk) := by
  unfold advancePreparation
  dsimp only
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · next hidx =>
      unfold preparedEnd
      dsimp only
      rw [UInt64.toNat_ofNat_of_lt' (by
        have : UInt64.size = 2 ^ 64 := rfl
        omega)]
      exact Nat.mul_le_mul_right _ (by omega)

/-- VAL-5, catalog form: while the next window still fits the
activation interval (and the successor index is representable), one
advancement strictly grows the prepared window — by exactly one bottom
tree. This is what moves `_sign_with_key`'s preparation loop forward. -/
theorem advancePreparation_strict_mono (s : Scheme)
    (hW : 0 < s.leavesPerBottomTree)
    (rebuild : SSZ.Uint64 → HashSubTree) (sk : SecretKey)
    (hin : (sk.leftBottomTreeIndex.toNat + 3) * s.leavesPerBottomTree ≤
      activationEnd sk)
    (hidx : sk.leftBottomTreeIndex.toNat + 2 < 2 ^ 64) :
    preparedEnd s sk < preparedEnd s (advancePreparation s rebuild sk) := by
  unfold advancePreparation
  dsimp only
  rw [if_neg (by omega), if_neg (by omega)]
  unfold preparedEnd
  dsimp only
  rw [UInt64.toNat_ofNat_of_lt' (by
    have : UInt64.size = 2 ^ 64 := rfl
    omega)]
  have h1 : sk.leftBottomTreeIndex.toNat + 2 < sk.leftBottomTreeIndex.toNat + 1 + 2 := by
    omega
  exact Nat.mul_lt_mul_of_lt_of_le h1 (Nat.le_refl _) hW

/-- Past the activation interval the key is a fixed point of
advancement ("returning the same key when no advancement is possible
keeps callers simple"). -/
theorem advancePreparation_exhausted (s : Scheme)
    (rebuild : SSZ.Uint64 → HashSubTree) (sk : SecretKey)
    (h : activationEnd sk <
      (sk.leftBottomTreeIndex.toNat + 3) * s.leavesPerBottomTree) :
    advancePreparation s rebuild sk = sk := by
  unfold advancePreparation
  exact if_pos h

end Scheme
end LeanSpec.Validator.Xmss
