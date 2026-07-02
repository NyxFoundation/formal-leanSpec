/-
SSZ power-of-two ceiling helper.

Mirrors `src/lean_spec/spec/crypto/merkleization.py` in leanSpec
(`_next_pow2`, formerly `get_power_of_two_ceil`):

  def _next_pow2(x: int) -> int:
      if x <= 1:
          return 1
      return 1 << (x - 1).bit_length()

For `x ≥ 2`, Python's `(x - 1).bit_length()` equals `(x - 1).log2 + 1` in
Lean, so `1 << (x - 1).bit_length()` is `2 ^ ((x - 1).log2 + 1)`. The result
pads Merkle-tree leaf counts up to the next power of two.

Proves SSZ-6 from `docs/lean4-proof-propositions.md`:
  - SSZ-6: `getPowerOfTwoCeil x` is the smallest power of two that is at
    least `x`: it is some `2 ^ k` with `x ≤ 2 ^ k`, and either `k = 0` or
    the next-smaller power `2 ^ (k - 1)` is strictly below `x`.
-/

namespace LeanSpec.SSZ

/-- Smallest power of two greater than or equal to `x`. Returns 1 for `x ≤ 1`. -/
def getPowerOfTwoCeil (x : Nat) : Nat :=
  if x ≤ 1 then 1 else 2 ^ ((x - 1).log2 + 1)

/--
SSZ-6: `getPowerOfTwoCeil x` is a power of two `2 ^ k` with `x ≤ 2 ^ k`,
and it is minimal — either `k = 0` or `2 ^ (k - 1) < x`.
-/
theorem ceil_pow2_minimal (x : Nat) (_h : 0 < x) :
    x ≤ getPowerOfTwoCeil x ∧
      ∃ k, getPowerOfTwoCeil x = 2 ^ k ∧ (k = 0 ∨ 2 ^ (k - 1) < x) := by
  unfold getPowerOfTwoCeil
  by_cases hx : x ≤ 1
  · rw [if_pos hx]
    exact ⟨hx, 0, rfl, Or.inl rfl⟩
  · rw [if_neg hx]
    have hne : x - 1 ≠ 0 := by omega
    have h_upper : x - 1 < 2 ^ ((x - 1).log2 + 1) := Nat.lt_log2_self
    have h_lower : 2 ^ (x - 1).log2 ≤ x - 1 := Nat.log2_self_le hne
    refine ⟨by omega, (x - 1).log2 + 1, rfl, Or.inr ?_⟩
    rw [Nat.add_sub_cancel]
    omega

end LeanSpec.SSZ
