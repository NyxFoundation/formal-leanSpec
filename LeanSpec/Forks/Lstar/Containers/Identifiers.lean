/-
Scalar identifiers naming validators and the registry index space.

Mirrors `src/lean_spec/spec/forks/lstar/containers/identifiers.py` in
leanSpec:
  - `ValidatorIndex.proposer_for_slot(slot, num_validators)`: round-robin
    proposer selection — the proposer is `slot % num_validators`. Upstream
    raises `EMPTY_VALIDATOR_REGISTRY` for an empty registry; in Lean the
    callers guard (`processBlockHeader` rejects before selecting).

`SubnetId` / `compute_subnet_id` and `is_within_registry` are added when a
proposition consumes them.

Proves VAL-1 and VAL-3 from `docs/lean4-proof-propositions.md`:
  - VAL-1: proposers are selected round-robin —
    `proposerForSlot slot n` is the validator index `slot % n`
    (`proposer_index_round_robin`), with the `toNat`-level corollary
    showing the `UInt64` construction never wraps.
  - VAL-3: each slot has exactly one proposer (`unique_proposer`).
-/

import LeanSpec.Aliases

namespace LeanSpec.Forks.Lstar

namespace ValidatorIndex

/-- Round-robin proposer selection (`proposer_for_slot`): the validator
responsible for proposing at `slot` in a registry of `numValidators`. -/
def proposerForSlot (slot : Slot) (numValidators : Nat) : ValidatorIndex :=
  UInt64.ofNat (slot.toNat % numValidators)

/-- VAL-1: proposers are selected round-robin. The catalog's
`ValidatorIndex.mk` is realized as `UInt64.ofNat` (`ValidatorIndex` is a
`Uint64`, as upstream). -/
theorem proposer_index_round_robin (slot : Slot) (n : Nat) (_h : 0 < n) :
    proposerForSlot slot n = UInt64.ofNat (slot.toNat % n) := rfl

/-- The round-robin index at the `Nat` level: the `UInt64` construction
never wraps, since `slot % n ≤ slot < 2^64`. -/
theorem proposerForSlot_toNat (slot : Slot) (n : Nat) :
    (proposerForSlot slot n).toNat = slot.toNat % n := by
  have h1 : slot.toNat % n ≤ slot.toNat := Nat.mod_le _ _
  have h2 : slot.toNat < 2 ^ 64 := slot.toNat_lt
  have h3 : UInt64.size = 2 ^ 64 := rfl
  exact UInt64.toNat_ofNat_of_lt' (by omega)

/-- Whether validator `vid`, in a registry of `n` validators, is the
scheduled proposer of `slot` (`is_proposer`: equality with
`proposer_for_slot`). Phrased on `Fin n` so registry membership is carried
by the type, per the catalog. -/
def isProposerFor {n : Nat} (vid : Fin n) (slot : Slot) : Prop :=
  vid.val = slot.toNat % n

/-- VAL-3: each slot has exactly one proposer — the round-robin index
exists and any proposer equals it. The catalog's `∃!` is written in its
expanded form (`ExistsUnique` lives in Mathlib, which this repo does not
depend on). -/
theorem unique_proposer (slot : Slot) (n : Nat) (h : 0 < n) :
    ∃ vid : Fin n, isProposerFor vid slot ∧
      ∀ vid' : Fin n, isProposerFor vid' slot → vid' = vid := by
  refine ⟨⟨slot.toNat % n, Nat.mod_lt _ h⟩, rfl, ?_⟩
  intro vid hvid
  exact Fin.ext hvid

end ValidatorIndex

end LeanSpec.Forks.Lstar
