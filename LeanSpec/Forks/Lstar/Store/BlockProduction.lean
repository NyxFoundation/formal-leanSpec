/-
Proposer-side block building: the fixed-point attestation selection.

Mirrors `build_block` in `src/lean_spec/spec/forks/lstar/block_production.py`
(post leanEthereum/leanSpec#1181, so candidate order and every tie-break
are content-derived, never arrival-order derived):
  - Selection is circular — a vote may only build from an
    already-justified source, yet including votes is the act that
    justifies those sources — so the proposer selects in rounds: pick
    eligible proofs, apply the state transition to a trial block,
    re-anchor on any newly justified checkpoint, and repeat until a pass
    adds nothing.
  - `candidatePrecedence` — candidates ordered once by
    `(target.slot, hash_tree_root(data))`.
  - `candidateEligible` — the per-candidate filter chain (head known,
    source at the current justified checkpoint, lies on chain, source
    justified, target not already justified — genesis self-votes exempt).
  - `selectionPass` — one pass of the `for` loop over the still
    unprocessed candidates, with the `MAX_ATTESTATIONS_DATA`
    proposer-side budget.
  - `selectionLoop` — the `while True` fixed point, defined by
    well-founded recursion on the number of unprocessed candidates: a
    pass that found nothing ends the loop, and a re-anchored pass
    re-enters with strictly fewer unprocessed candidates
    (`selectionPass_rest_lt`). No fuel is involved — Lean accepts the
    definition only because the iteration provably terminates, which is
    upstream's own argument: "the chosen set only grows, and is bounded".
  - `buildBlockAttestations` — `build_block`'s setup (slot advancement,
    genesis anchoring, justified-window extension, chain-view assembly,
    candidate sort) feeding the loop.

Divergences from Python, documented per function:
  - Python re-scans the full sorted candidate list each pass, skipping
    the `processed_attestation_data` set; here each pass consumes the
    accepted candidates and returns the rest in order — equivalent,
    since candidates are distinct `dict` keys and the order is fixed
    up front.
  - The coverage picker (`select_proofs_for_coverage`,
    `src/lean_spec/spec/forks/lstar/aggregation.py`) is a parameter
    (`selectProofs`): it is proposer-local optimization whose choices
    never affect the loop's control flow (a pass continues on which
    *data* were accepted, not which proofs), and its tie-break needs
    `encode_bytes` of XMSS aggregates (Arklib side). FC-5 therefore
    holds for every picker.
  - The post-loop collapse (one merged attestation per data) and the
    signing wrapper are packaging outside the fixed point and are not
    modeled.
  - `slot - 1` and the empty-slot count use wrapping `UInt64` / truncated
    `Nat` subtraction where Python would raise on underflow; production
    calls sit at `slot ≥ 1` past the latest header, as upstream assumes.

Proves FC-5 from `docs/lean4-proof-propositions.md`:
  - FC-5: the block-production iteration terminates in finitely many
    rounds — witnessed by `selectionLoop`'s well-founded recursion, and
    stated explicitly as `build_block_selection_terminates`: the loop
    runs at most `payloads.length + 1` passes.
-/

import LeanSpec.Forks.Lstar.Containers.Aggregation
import LeanSpec.Forks.Lstar.StateTransition
import LeanSpec.SSZ.Hash

namespace LeanSpec.Forks.Lstar
namespace BlockProduction

/-- One selection candidate: an attestation data with the proofs
available for it (`aggregated_payloads.items()`). -/
abbrev Candidate := AttestationData × List SingleMessageAggregate

/-- Ascending candidate order: target slot first, the canonical
attestation-data root breaking ties (`sorted(..., key=(target.slot,
hash_tree_root))`) — so every node builds the same block and the budget
cutoff is content-derived (leanEthereum/leanSpec#1181). -/
def candidatePrecedence [SSZ.HasHashTreeRoot AttestationData]
    (a b : Candidate) : Bool :=
  decide (a.1.target.slot < b.1.target.slot) ||
  (a.1.target.slot == b.1.target.slot &&
    Root.lexLe (SSZ.hashTreeRoot a.1) (SSZ.hashTreeRoot b.1))

/-- Loop-carried selection state: the justified/finalized anchor the
filters run against, the distinct-data count against the budget, and
the accumulated per-pass output lists. -/
structure SelectionState where
  justifiedCheckpoint : Checkpoint
  justifiedSlots : JustifiedSlots
  finalizedSlot : Slot
  processedCount : Nat
  attestations : List AggregatedAttestation
  signatures : List SingleMessageAggregate

/-- The per-candidate filter chain of the selection `for` body: `.ok
true` accepts, `.ok false` skips (upstream `continue`), and an
out-of-window justification query rejects the build, as in Python. The
order is upstream's: head known, source at the justified checkpoint,
lies on chain, source justified, then target not already justified —
with genesis self-votes (source and target both at slot 0) exempt from
the target check, kept for their head weight. -/
def candidateEligible (chainView : Array Root) (knownRoots : List Root)
    (ps : SelectionState) (data : AttestationData) : ST.Result Bool :=
  -- Skip votes whose head block the proposer has not seen.
  if !(knownRoots.contains data.head.root) then .ok false
  -- Skip votes whose source is not the current justified checkpoint.
  else if data.source.slot ≠ ps.justifiedCheckpoint.slot then .ok false
  -- Reject votes that do not match this chain (also bounds the lookups).
  else if !(data.liesOnChain chainView) then .ok false
  else
    -- A vote may only build from an already-justified source.
    match JustifiedSlots.isSlotJustified ps.justifiedSlots ps.finalizedSlot
        data.source.slot with
    | .error e => .error e
    | .ok false => .ok false
    | .ok true =>
      -- Genesis self-votes justify nothing but carry head weight.
      if data.source.slot == 0 && data.target.slot == 0 then .ok true
      else
        -- A justified target gains nothing from more votes.
        match JustifiedSlots.isSlotJustified ps.justifiedSlots
            ps.finalizedSlot data.target.slot with
        | .error e => .error e
        | .ok justified => .ok !justified

/-- One pass over the unprocessed candidates (the `for` loop of a
round): the budget stops the pass, a skipped candidate stays
unprocessed in order, an accepted one contributes its proofs and is
consumed. Returns the updated state, the candidates still unprocessed,
and whether anything was accepted (`found_new_entries`). -/
def selectionPass (chainView : Array Root) (knownRoots : List Root)
    (selectProofs : List SingleMessageAggregate → List SingleMessageAggregate) :
    SelectionState → List Candidate →
    ST.Result (SelectionState × List Candidate × Bool)
  | ps, [] => .ok (ps, [], false)
  | ps, c :: cs =>
    -- The distinct-data cap is a proposer-side budget, not a consensus
    -- rule; reaching it ends the pass.
    if MAX_ATTESTATIONS_DATA ≤ ps.processedCount then
      .ok (ps, c :: cs, false)
    else
      match candidateEligible chainView knownRoots ps c.1 with
      | .error e => .error e
      | .ok false =>
        match selectionPass chainView knownRoots selectProofs ps cs with
        | .error e => .error e
        | .ok (ps', rest, foundNew) => .ok (ps', c :: rest, foundNew)
      | .ok true =>
        -- Choose proofs covering the most validators; one attestation
        -- per chosen proof.
        let selected := selectProofs c.2
        let ps' := { ps with
          processedCount := ps.processedCount + 1
          signatures := ps.signatures ++ selected
          attestations := ps.attestations ++ selected.map (fun proof =>
            { aggregationBits := proof.participants, data := c.1 }) }
        match selectionPass chainView knownRoots selectProofs ps' cs with
        | .error e => .error e
        | .ok (ps'', rest, _) => .ok (ps'', rest, true)

/-- A pass never lengthens the unprocessed list. -/
theorem selectionPass_rest_le (chainView : Array Root)
    (knownRoots : List Root)
    (selectProofs : List SingleMessageAggregate → List SingleMessageAggregate) :
    ∀ (l : List Candidate) (ps ps' : SelectionState)
      (rest : List Candidate) (foundNew : Bool),
    selectionPass chainView knownRoots selectProofs ps l
      = .ok (ps', rest, foundNew) →
    rest.length ≤ l.length
  | [], ps, ps', rest, foundNew, h => by
    injection h with h'
    injection h' with _ h''
    injection h'' with hrest _
    rw [← hrest]
    exact Nat.le_refl _
  | c :: cs, ps, ps', rest, foundNew, h => by
    rw [selectionPass] at h
    split at h
    · injection h with h'
      injection h' with _ h''
      injection h'' with hrest _
      rw [← hrest]
      exact Nat.le_refl _
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · next ps₁ rest₁ fn₁ hrec =>
          injection h with h'
          injection h' with _ h''
          injection h'' with hrest _
          rw [← hrest]
          exact Nat.succ_le_succ
            (selectionPass_rest_le chainView knownRoots selectProofs cs
              ps ps₁ rest₁ fn₁ hrec)
      · dsimp only at h
        split at h
        · exact absurd h (by simp)
        · next ps₂ rest₂ fn₂ hrec =>
          injection h with h'
          injection h' with _ h''
          injection h'' with hrest _
          rw [← hrest]
          exact Nat.le_succ_of_le
            (selectionPass_rest_le chainView knownRoots selectProofs cs
              _ ps₂ rest₂ fn₂ hrec)

/-- A pass that accepted something strictly shrinks the unprocessed
list — the decreasing measure of the fixed-point loop. -/
theorem selectionPass_rest_lt (chainView : Array Root)
    (knownRoots : List Root)
    (selectProofs : List SingleMessageAggregate → List SingleMessageAggregate) :
    ∀ (l : List Candidate) (ps ps' : SelectionState)
      (rest : List Candidate),
    selectionPass chainView knownRoots selectProofs ps l
      = .ok (ps', rest, true) →
    rest.length < l.length
  | [], ps, ps', rest, h => by
    injection h with h'
    injection h' with _ h''
    injection h'' with _ hfn
    exact absurd hfn (by simp)
  | c :: cs, ps, ps', rest, h => by
    rw [selectionPass] at h
    split at h
    · injection h with h'
      injection h' with _ h''
      injection h'' with _ hfn
      exact absurd hfn (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · next ps₁ rest₁ fn₁ hrec =>
          injection h with h'
          injection h' with _ h''
          injection h'' with hrest hfn
          rw [← hrest]
          rw [hfn] at hrec
          exact Nat.succ_lt_succ
            (selectionPass_rest_lt chainView knownRoots selectProofs cs
              ps ps₁ rest₁ hrec)
      · dsimp only at h
        split at h
        · exact absurd h (by simp)
        · next ps₂ rest₂ fn₂ hrec =>
          injection h with h'
          injection h' with _ h''
          injection h'' with hrest _
          rw [← hrest]
          exact Nat.lt_succ_of_le
            (selectionPass_rest_le chainView knownRoots selectProofs cs
              _ ps₂ rest₂ fn₂ hrec)

/-- The `while True` fixed point of `build_block`, by well-founded
recursion on the unprocessed candidate count — no fuel. A pass that
found nothing ends the loop; a pass that advanced justification or
finalization re-anchors and re-enters on the strictly smaller remainder
(`selectionPass_rest_lt`). Also counts the passes executed, so the
FC-5 bound can be stated about it. -/
def selectionLoop (advancedState : State) (slot : Slot)
    (proposerIndex : ValidatorIndex) (parentRoot : Root)
    (chainView : Array Root) (knownRoots : List Root)
    (selectProofs : List SingleMessageAggregate → List SingleMessageAggregate)
    (ps : SelectionState) (unprocessed : List Candidate) :
    ST.Result (SelectionState × Nat) :=
  match _hpass : selectionPass chainView knownRoots selectProofs ps
      unprocessed with
  | .error e => .error e
  | .ok (ps', rest, foundNew) =>
    if _hfn : foundNew then
      -- Apply the state transition to a trial block; its post-state
      -- reveals whether this pass advanced justification.
      let candidateBlock : Block := {
        slot := slot
        proposerIndex := proposerIndex
        parentRoot := parentRoot
        stateRoot := SSZ.Bytes32.zero
        body := { attestations := ps'.attestations.toArray } }
      match State.processBlock advancedState candidateBlock with
      | .error e => .error e
      | .ok post =>
        -- Repeat only if justification or finalization moved; both
        -- advance monotonically, so the loop is bounded.
        if !(post.latestJustified == ps'.justifiedCheckpoint) ||
            !(post.latestFinalized.slot == ps'.finalizedSlot) then
          match selectionLoop advancedState slot proposerIndex parentRoot
              chainView knownRoots selectProofs
              { ps' with
                justifiedCheckpoint := post.latestJustified
                justifiedSlots := post.justifiedSlots
                finalizedSlot := post.latestFinalized.slot }
              rest with
          | .error e => .error e
          | .ok (psFinal, n) => .ok (psFinal, n + 1)
        else .ok (ps', 1)
    else .ok (ps', 1)
termination_by unprocessed.length
decreasing_by
  exact selectionPass_rest_lt chainView knownRoots selectProofs unprocessed
    ps ps' rest (_hfn ▸ _hpass)

/-- The loop runs at most one pass per candidate plus the closing pass:
every re-entry consumed at least one candidate. -/
theorem selectionLoop_passes_le (advancedState : State) (slot : Slot)
    (proposerIndex : ValidatorIndex) (parentRoot : Root)
    (chainView : Array Root) (knownRoots : List Root)
    (selectProofs : List SingleMessageAggregate → List SingleMessageAggregate) :
    ∀ (k : Nat) (unprocessed : List Candidate),
      unprocessed.length ≤ k →
    ∀ (ps psFinal : SelectionState) (n : Nat),
    selectionLoop advancedState slot proposerIndex parentRoot chainView
      knownRoots selectProofs ps unprocessed = .ok (psFinal, n) →
    n ≤ unprocessed.length + 1 := by
  intro k
  induction k with
  | zero =>
    intro l hl ps psFinal n h
    rw [selectionLoop] at h
    split at h
    · exact absurd h (by simp)
    · next ps' rest foundNew hpass =>
      split at h
      · next hfn =>
        exfalso
        have hlt := selectionPass_rest_lt chainView knownRoots selectProofs
          l ps ps' rest (hfn ▸ hpass)
        omega
      · injection h with h'
        injection h' with _ hn
        omega
  | succ k ih =>
    intro l hl ps psFinal n h
    rw [selectionLoop] at h
    split at h
    · exact absurd h (by simp)
    · next ps' rest foundNew hpass =>
      split at h
      · next hfn =>
        have hlt := selectionPass_rest_lt chainView knownRoots selectProofs
          l ps ps' rest (hfn ▸ hpass)
        dsimp only at h
        split at h
        · exact absurd h (by simp)
        · split at h
          · split at h
            · exact absurd h (by simp)
            · next psF n' hrec =>
              injection h with h'
              injection h' with _ hn
              have := ih rest (by omega) _ psF n' hrec
              omega
          · injection h with h'
            injection h' with _ hn
            omega
      · injection h with h'
        injection h' with _ hn
        omega

/-- `build_block`'s setup feeding the fixed point: advance the pre-state
to the block's slot, anchor on the checkpoint this chain treats as
justified (the parent at slot 0 on genesis), extend the justified
window to every slot the loop may query, assemble the chain view as it
will look once this block is applied, order the candidates once, and
run the selection rounds. Returns the final selection state and the
number of passes executed. -/
def buildBlockAttestations [SSZ.HasHashTreeRoot AttestationData]
    (state : State) (slot : Slot) (proposerIndex : ValidatorIndex)
    (parentRoot : Root) (knownRoots : List Root)
    (payloads : List Candidate)
    (selectProofs : List SingleMessageAggregate → List SingleMessageAggregate) :
    ST.Result (SelectionState × Nat) :=
  let advancedState := State.processSlots state slot
  -- On genesis the parent is justified at slot 0 by header processing.
  let justifiedCheckpoint :=
    if state.latestBlockHeader.slot = 0 then
      ({ root := parentRoot, slot := 0 } : Checkpoint)
    else state.latestJustified
  let finalizedSlot := state.latestFinalized.slot
  -- Extend the window so every slot the loop may query is covered.
  let justifiedSlots :=
    JustifiedSlots.extendToSlot state.justifiedSlots finalizedSlot (slot - 1)
  -- History up to the parent, the parent root, then a zero hash per
  -- skipped slot (the chain as it will look once this block applies).
  let numEmptySlots := slot.toNat - state.latestBlockHeader.slot.toNat - 1
  let chainView :=
    (state.historicalBlockHashes.push parentRoot) ++
      Array.replicate numEmptySlots SSZ.Bytes32.zero
  selectionLoop advancedState slot proposerIndex parentRoot chainView
    knownRoots selectProofs
    { justifiedCheckpoint := justifiedCheckpoint
      justifiedSlots := justifiedSlots
      finalizedSlot := finalizedSlot
      processedCount := 0
      attestations := []
      signatures := [] }
    (payloads.mergeSort candidatePrecedence)

/-- FC-5: the block-production iteration terminates in finitely many
rounds. Termination itself is witnessed by `selectionLoop`'s
well-founded recursion (Lean accepts the definition with no fuel); this
theorem states the explicit bound — the fixed point is reached within
one pass per candidate attestation data plus the closing pass, for any
coverage picker. -/
theorem build_block_selection_terminates
    [SSZ.HasHashTreeRoot AttestationData]
    (state : State) (slot : Slot) (proposerIndex : ValidatorIndex)
    (parentRoot : Root) (knownRoots : List Root)
    (payloads : List Candidate)
    (selectProofs : List SingleMessageAggregate → List SingleMessageAggregate)
    (psFinal : SelectionState) (n : Nat)
    (h : buildBlockAttestations state slot proposerIndex parentRoot
      knownRoots payloads selectProofs = .ok (psFinal, n)) :
    n ≤ payloads.length + 1 := by
  unfold buildBlockAttestations at h
  dsimp only at h
  have hbound := selectionLoop_passes_le _ _ _ _ _ _ _
    (payloads.mergeSort candidatePrecedence).length
    (payloads.mergeSort candidatePrecedence) (Nat.le_refl _) _ psFinal n h
  rw [List.length_mergeSort] at hbound
  exact hbound

end BlockProduction
end LeanSpec.Forks.Lstar
