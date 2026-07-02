/-
Slot justifiability judgments (3SF-mini).

Mirrors `src/lean_spec/spec/forks/lstar/slot.py` in leanSpec:
  - `IMMEDIATE_JUSTIFICATION_WINDOW = 5`
  - `Slot.is_justifiable_after(finalized_slot)`: a slot is a justification
    candidate iff its distance δ from the last finalized slot satisfies
    δ ≤ 5, δ is a perfect square, or δ is pronic (`n(n+1)`, detected via
    `4δ + 1` being an odd perfect square).
  - `Slot.justified_index_after(finalized_slot)`: relative bitfield index
    for justification tracking; `none` at or before the finalized boundary.

Python states both as methods on the candidate slot; the catalog (CONT-2)
uses the argument order `(finalized, target)`, adopted here. Python asserts
`target ≥ finalized` in `is_justifiable_after`; in Lean the `Nat`
subtraction truncates instead — callers guarantee the precondition, as
upstream's assert documents.

Supports the ST-* and CONT-2 propositions from
`docs/lean4-proof-propositions.md` (no theorems in this file).
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
(`is_justifiable_after`). -/
def isJustifiableAfter (finalized target : Slot) : Bool :=
  justifiableDelta (target.toNat - finalized.toNat)

/-- Relative bitfield index of `target` for justification tracking
(`justified_index_after`). Slots at or before the finalized boundary are
implicitly justified and carry no index. -/
def justifiedIndexAfter (finalized target : Slot) : Option Nat :=
  if target ≤ finalized then none
  else some (target.toNat - finalized.toNat - 1)

end LeanSpec.Slot
