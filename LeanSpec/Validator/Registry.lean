/-
Validator key registry (the dual-key configuration).

Mirrors `src/lean_spec/node/validator/registry.py`:
  - `ValidatorEntry` — a validator's key material: "Attestation and
    proposal keys are separate. This lets one validator sign both
    within the same slot without OTS conflict."
  - `ValidatorRegistry` — the signing keys this node controls: a map
    from validator index to entry, with `add` replacing any existing
    entry with the same index. The upstream `dict` is keyed by
    `entry.index` at every insertion site, so the model stores the
    entries directly and looks them up by their own index.

Upstream states the dual-key separation but does not enforce it:
`add` is a bare assignment and `from_yaml` raises only for missing
files and decode failures — a same-key manifest loads silently and
then signs a proposal and an attestation for one slot with one
stateful XMSS key (OTS state reuse; found by attempting VAL-2, an
"invariant maintained only by convention" of the same class as
leanEthereum/leanSpec#1176, reported upstream). The distinctness
therefore enters as `WellFormed`, and `WellFormed.add` shows the
suggested fix — validating at insertion — preserves it.

Proves VAL-2 from `docs/lean4-proof-propositions.md`:
  - VAL-2: on a well-formed registry, every lookup returns an entry
    whose proposal key differs from its attestation key
    (`dual_key_distinct`).
-/

import LeanSpec.Validator.Xmss

namespace LeanSpec.Validator

open Xmss (SecretKey)

/-- A single validator's key material (`ValidatorEntry`): attestation
and proposal keys are separate so one validator can sign both within
the same slot without one-time-signature conflict. -/
structure ValidatorEntry where
  index : ValidatorIndex
  attestationSecretKey : SecretKey
  proposalSecretKey : SecretKey
  deriving Inhabited

/-- Signing keys for the validators this node controls
(`ValidatorRegistry`). -/
structure ValidatorRegistry where
  validators : List ValidatorEntry
  deriving Inhabited

namespace ValidatorRegistry

/-- Add a validator entry, replacing any existing entry with the same
index (`add`; the upstream `dict` assignment). -/
def add (reg : ValidatorRegistry) (entry : ValidatorEntry) :
    ValidatorRegistry :=
  { validators :=
      entry :: reg.validators.filter (fun e => !(e.index == entry.index)) }

/-- Return the validator entry for an index, or `none` if this node
does not control it (`get`). -/
def get? (reg : ValidatorRegistry) (index : ValidatorIndex) :
    Option ValidatorEntry :=
  reg.validators.find? (fun e => e.index == index)

/-- The dual-key separation `ValidatorEntry` documents but upstream
does not enforce: every entry's proposal key differs from its
attestation key. A same-key entry would let one slot's proposal and
attestation signatures consume overlapping XMSS one-time-signature
state (see the module docstring). -/
def WellFormed (reg : ValidatorRegistry) : Prop :=
  ∀ e ∈ reg.validators, e.proposalSecretKey ≠ e.attestationSecretKey

/-- VAL-2: on a well-formed registry, the key a validator signs
proposals with is never the key it signs attestations with. -/
theorem dual_key_distinct (reg : ValidatorRegistry)
    (hwf : WellFormed reg) (index : ValidatorIndex)
    (entry : ValidatorEntry) (h : reg.get? index = some entry) :
    entry.proposalSecretKey ≠ entry.attestationSecretKey := by
  unfold get? at h
  exact hwf entry (List.mem_of_find?_eq_some h)

/-- The suggested upstream fix preserves well-formedness: inserting an
entry whose keys are distinct into a well-formed registry keeps every
entry's keys distinct — insertion is where the invariant is one cheap
comparison to enforce. -/
theorem WellFormed.add (reg : ValidatorRegistry) (entry : ValidatorEntry)
    (hwf : WellFormed reg)
    (hentry : entry.proposalSecretKey ≠ entry.attestationSecretKey) :
    WellFormed (reg.add entry) := by
  intro e he
  cases List.mem_cons.mp he with
  | inl heq => rw [heq]; exact hentry
  | inr hmem => exact hwf e (List.mem_filter.mp hmem).1

end ValidatorRegistry
end LeanSpec.Validator
