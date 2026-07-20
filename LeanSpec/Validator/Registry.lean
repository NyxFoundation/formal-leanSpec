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

Upstream originally stated the dual-key separation but did not
enforce it: `add` was a bare assignment and `from_yaml` raised only
for missing files and decode failures — a same-key manifest loaded
silently and then signed a proposal and an attestation for one slot
with one stateful XMSS key (OTS state reuse; found by attempting
VAL-2, an "invariant maintained only by convention" of the same class
as leanEthereum/leanSpec#1176, reported as #1184). Since
leanEthereum/leanSpec#1185 the loader rejects such a manifest by
comparing its two public keys (the secret bytes stay untouched), so
every loaded registry satisfies the distinctness by construction.
The distinctness enters the theorems as `WellFormed`; `WellFormed.add`
shows unchecked insertion preserves it, and `addChecked` mirrors the
merged load-time check.

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

/-- The dual-key separation `ValidatorEntry` documents and the loader
enforces since leanEthereum/leanSpec#1185: every entry's proposal key
differs from its attestation key. A same-key entry would let one
slot's proposal and attestation signatures consume overlapping XMSS
one-time-signature state (see the module docstring). -/
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

/-! ## Checked insertion (the merged fix of leanEthereum/leanSpec#1185)

Mirrors the fix merged upstream as leanEthereum/leanSpec#1185 (closes
#1184): `from_yaml` rejects a manifest entry whose attestation and
proposal public keys coincide, before any secret key is decoded. The
public-key derivation is Arklib-side crypto, so it enters the model as
the `publicKeyOf` parameter. Distinct public keys imply distinct
secret keys for *every* derivation (a function maps equal inputs to
equal outputs), so `WellFormed` follows with no cryptographic
assumption; the OTS-level content — distinct master seeds — follows
for derivations that fingerprint the seed
(`addChecked_seed_distinct`). -/

/-- Add a validator entry only when its two public keys differ — the
load-time validation of leanEthereum/leanSpec#1185. `none` mirrors the
`ValueError` the loader raises on a same-key manifest; the comparison
touches only public material. -/
def addChecked (publicKeyOf : SecretKey → ByteArray)
    (reg : ValidatorRegistry) (entry : ValidatorEntry) :
    Option ValidatorRegistry :=
  if (publicKeyOf entry.attestationSecretKey).data ==
      (publicKeyOf entry.proposalSecretKey).data then
    none
  else
    some (reg.add entry)

/-- The checked insertion discharges the `WellFormed` distinctness at
construction, for every public-key derivation: an accepted entry has
distinct public keys, and equal secret keys cannot derive distinct
public keys. Upstream now enforces the check, so every loaded registry
is well-formed by construction — closing the loop the way
leanEthereum/leanSpec#1179 did for the store invariants. -/
theorem addChecked_wellFormed (publicKeyOf : SecretKey → ByteArray)
    (reg reg' : ValidatorRegistry)
    (entry : ValidatorEntry) (hwf : WellFormed reg)
    (h : addChecked publicKeyOf reg entry = some reg') :
    WellFormed reg' := by
  unfold addChecked at h
  split at h
  · simp at h
  · next hne =>
    injection h with h'
    subst h'
    exact WellFormed.add reg entry hwf fun hc =>
      hne (by rw [hc]; exact beq_self_eq_true _)

/-- The OTS-reuse core of leanEthereum/leanSpec#1184: when the
derivation fingerprints the master seed (Arklib derives the public
root from the PRF seed), an accepted entry's two keys have distinct
seeds, so one slot's proposal and attestation signatures can never
consume overlapping one-time-signature state. -/
theorem addChecked_seed_distinct (publicKeyOf : SecretKey → ByteArray)
    (hdet : ∀ k₁ k₂ : SecretKey, k₁.prfKey.data = k₂.prfKey.data →
      publicKeyOf k₁ = publicKeyOf k₂)
    (reg reg' : ValidatorRegistry) (entry : ValidatorEntry)
    (h : addChecked publicKeyOf reg entry = some reg') :
    entry.proposalSecretKey.prfKey.data ≠
      entry.attestationSecretKey.prfKey.data := by
  unfold addChecked at h
  split at h
  · simp at h
  · next hne =>
    intro hseed
    exact hne (by rw [hdet _ _ hseed]; exact beq_self_eq_true _)

end ValidatorRegistry
end LeanSpec.Validator
