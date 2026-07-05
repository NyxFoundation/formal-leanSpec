/-
Slot justifiability judgments (3SF-mini).

Mirrors `src/lean_spec/spec/forks/lstar/slot.py` in leanSpec:
  - `IMMEDIATE_JUSTIFICATION_WINDOW = 5`
  - `Slot.is_justifiable_after(finalized_slot)`: a slot before the
    finalized boundary is already settled and never a candidate; past it,
    a slot is a justification candidate iff its distance δ from the last
    finalized slot satisfies δ ≤ 5, δ is a perfect square, or δ is pronic
    (`n(n+1)`, detected via `4δ + 1` being an odd perfect square).
  - `Slot.justified_index_after(finalized_slot)`: relative bitfield index
    for justification tracking; `none` at or before the finalized boundary.

Python states both as methods on the candidate slot; the catalog (CONT-2)
uses the argument order `(finalized, target)`, adopted here.
`is_justifiable_after` is total since leanEthereum/leanSpec#1178
(previously it asserted `target ≥ finalized`): a slot below the finalized
boundary returns `False` instead of raising. `isJustifiableAfter` carries
the same guard, proved as `justifiable_before_finalized`.

Proves CONT-2 from `docs/lean4-proof-propositions.md`:
  - CONT-2: past the finalized boundary, `Slot.isJustifiableAfter
    finalized target` holds iff the slot distance is at most 5, a perfect
    square, or a pronic number (`justifiable_iff`), via correctness of the
    hand-rolled `isqrt`; below the boundary it is `false`
    (`justifiable_before_finalized`).

Also supports the ST-* propositions (the executable judgments are consumed
by `process_attestations`).
-/

import LeanSpec.Aliases

namespace LeanSpec.Slot

/-- First N slots after finalization are always justifiable
(`IMMEDIATE_JUSTIFICATION_WINDOW`). -/
def immediateJustificationWindow : Nat := 5

/-- Integer square root (Python `math.isqrt`): the largest `r` with
`r * r ≤ n`. Lean core has no `Nat` square root, so it is defined here by
the classic base-4 recursion. -/
def isqrt (n : Nat) : Nat :=
  if n ≤ 1 then n
  else
    let small := 2 * isqrt (n / 4)
    let large := small + 1
    if large * large ≤ n then large else small
decreasing_by
  exact Nat.div_lt_self (by omega) (by omega)

/-- Justifiability of a slot distance `δ` from the finalized slot:
within the immediate window, a perfect square, or a pronic number. -/
def justifiableDelta (delta : Nat) : Bool :=
  decide (delta ≤ immediateJustificationWindow) ||
  isqrt delta * isqrt delta == delta ||
  (let discriminant := 4 * delta + 1
   let root := isqrt discriminant
   root * root == discriminant && root % 2 == 1)

/-- Whether `target` is a valid justification candidate after `finalized`
(`is_justifiable_after`). A slot before the finalized boundary is already
settled, never a future candidate. -/
def isJustifiableAfter (finalized target : Slot) : Bool :=
  if target < finalized then false
  else justifiableDelta (target.toNat - finalized.toNat)

/-- Relative bitfield index of `target` for justification tracking
(`justified_index_after`). Slots at or before the finalized boundary are
implicitly justified and carry no index. -/
def justifiedIndexAfter (finalized target : Slot) : Option Nat :=
  if target ≤ finalized then none
  else some (target.toNat - finalized.toNat - 1)

/-! ## CONT-2: characterization of justifiability -/

/-- Expand `(k + 1)²` so `omega` can reason with `k * k` as an atom. -/
private theorem sq_succ (k : Nat) : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
  rw [Nat.mul_succ, Nat.succ_mul]
  omega

/-- Expand an odd square: `(2m + 1)² = 4m² + 4m + 1`. -/
private theorem odd_sq (m : Nat) :
    (2 * m + 1) * (2 * m + 1) = 4 * (m * m) + 4 * m + 1 := by
  rw [sq_succ (2 * m), Nat.mul_mul_mul_comm]
  omega

/-- `isqrt` lower bound: its square never exceeds the input. -/
theorem isqrt_le (n : Nat) : isqrt n * isqrt n ≤ n := by
  induction n using isqrt.induct with
  | case1 n h =>
    rw [isqrt, if_pos h]
    have h01 : n = 0 ∨ n = 1 := by omega
    cases h01 with
    | inl h0 => subst h0; exact Nat.le_refl _
    | inr h1 => subst h1; exact Nat.le_refl _
  | case2 n h small large hlarge ih =>
    rw [isqrt, if_neg h]
    dsimp only
    split
    · next h2 => exact h2
    · next h2 => exact absurd hlarge h2
  | case3 n h small large hnlarge ih =>
    rw [isqrt, if_neg h]
    dsimp only
    split
    · next h2 => exact absurd h2 hnlarge
    · next h2 =>
      have hexp : (2 * isqrt (n / 4)) * (2 * isqrt (n / 4))
          = 4 * (isqrt (n / 4) * isqrt (n / 4)) := by
        rw [Nat.mul_mul_mul_comm]
      omega

/-- `isqrt` upper bound: the next square is strictly above the input. -/
theorem isqrt_lt_succ (n : Nat) : n < (isqrt n + 1) * (isqrt n + 1) := by
  induction n using isqrt.induct with
  | case1 n h =>
    rw [isqrt, if_pos h]
    rw [sq_succ]
    omega
  | case2 n h small large hlarge ih =>
    rw [isqrt, if_neg h]
    dsimp only
    split
    · rw [show 2 * isqrt (n / 4) + 1 + 1 = 2 * (isqrt (n / 4) + 1) from by omega,
          Nat.mul_mul_mul_comm]
      omega
    · next h2 => exact absurd hlarge h2
  | case3 n h small large hnlarge ih =>
    rw [isqrt, if_neg h]
    dsimp only
    split
    · next h2 => exact absurd h2 hnlarge
    · next h2 => exact Nat.lt_of_not_le h2

/-- `isqrt` is the unique value between the bracketing squares. -/
theorem isqrt_eq (k n : Nat) (h1 : k * k ≤ n) (h2 : n < (k + 1) * (k + 1)) :
    isqrt n = k := by
  have hle := isqrt_le n
  have hlt := isqrt_lt_succ n
  have h3 : ¬ isqrt n < k := fun hc => by
    have hstep : (isqrt n + 1) * (isqrt n + 1) ≤ k * k :=
      Nat.mul_le_mul (Nat.succ_le_of_lt hc) (Nat.succ_le_of_lt hc)
    omega
  have h4 : ¬ k < isqrt n := fun hc => by
    have hstep : (k + 1) * (k + 1) ≤ isqrt n * isqrt n :=
      Nat.mul_le_mul (Nat.succ_le_of_lt hc) (Nat.succ_le_of_lt hc)
    omega
  omega

/-- The pronic discriminant identity: `4k(k+1) + 1 = (2k+1)²`. -/
private theorem pronic_disc (k : Nat) :
    4 * (k * (k + 1)) + 1 = (2 * k + 1) * (2 * k + 1) := by
  rw [Nat.mul_succ, odd_sq]
  omega

/-- The three-form characterization of `justifiableDelta`: the distance is
within the immediate window, a perfect square, or a pronic number. -/
theorem justifiableDelta_iff (δ : Nat) :
    justifiableDelta δ = true ↔
      δ ≤ 5 ∨ (∃ k, δ = k * k) ∨ (∃ k, δ = k * (k + 1)) := by
  unfold justifiableDelta immediateJustificationWindow
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro h
    match h with
    | .inl (.inl h5) => exact .inl h5
    | .inl (.inr hsq) => exact .inr (.inl ⟨isqrt δ, hsq.symm⟩)
    | .inr ⟨hsq, hodd⟩ =>
      refine .inr (.inr ?_)
      have hm : isqrt (4 * δ + 1) = 2 * (isqrt (4 * δ + 1) / 2) + 1 := by
        omega
      refine ⟨isqrt (4 * δ + 1) / 2, ?_⟩
      rw [hm, odd_sq] at hsq
      rw [Nat.mul_succ]
      omega
  · intro h
    match h with
    | .inl h5 => exact .inl (.inl h5)
    | .inr (.inl ⟨k, hk⟩) =>
      refine .inl (.inr ?_)
      subst hk
      rw [isqrt_eq k (k * k) (Nat.le_refl _) (by rw [sq_succ k]; omega)]
    | .inr (.inr ⟨k, hk⟩) =>
      refine .inr ?_
      subst hk
      have hr : isqrt (4 * (k * (k + 1)) + 1) = 2 * k + 1 := by
        rw [pronic_disc]
        exact isqrt_eq (2 * k + 1) _ (Nat.le_refl _) (by
          rw [odd_sq, show 2 * k + 1 + 1 = 2 * (k + 1) from by omega,
              Nat.mul_mul_mul_comm, sq_succ k]
          omega)
      constructor
      · rw [hr]
        exact (pronic_disc k).symm
      · rw [hr]
        omega

/-- CONT-2: past the finalized boundary, `is_justifiable_after` holds iff
the slot distance from the finalized slot is at most 5, a perfect square,
or a pronic number. The `finalized ≤ target` hypothesis discharges the
settled-slot guard. -/
theorem justifiable_iff
    (finalized target : Slot) (h : finalized ≤ target) :
    isJustifiableAfter finalized target ↔
      (let δ := target.toNat - finalized.toNat
       δ ≤ 5 ∨ (∃ k, δ = k * k) ∨ (∃ k, δ = k * (k + 1))) := by
  unfold isJustifiableAfter
  rw [if_neg (UInt64.not_lt.mpr h)]
  exact justifiableDelta_iff (target.toNat - finalized.toNat)

/-- A slot strictly before the finalized boundary is never a justification
candidate — the settled-slot guard `is_justifiable_after` gained in
leanEthereum/leanSpec#1178 (previously an `assert` crash). -/
theorem justifiable_before_finalized
    (finalized target : Slot) (h : target < finalized) :
    isJustifiableAfter finalized target = false := by
  unfold isJustifiableAfter
  rw [if_pos h]

end LeanSpec.Slot
