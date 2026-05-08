---
title: Simplex Consensus → Lean4 Correctness Proposition Catalog
last_updated: 2026-05-09
tags:
  - lean4
  - formal-verification
  - simplex
  - consensus
  - safety
  - liveness
---

# Simplex Consensus → Lean4 Correctness Proposition Catalog

## Context

[Simplex Consensus](https://simplex.blog/protocol/) (Chan & Pass, IACR ePrint 2023/463)
is the partially-synchronous BFT protocol that the Lean Ethereum consensus layer is built
around. The "Correctness of the Protocol" section of the blog post and the matching
section of the paper give two arguments — **Consistency** (a safety property) and
**Liveness** — each broken into a small number of named claims.

This document is a catalog of those correctness claims, expressed as Lean 4 theorem
skeletons (`theorem ... := by sorry`). It mirrors the structure of
`docs/lean4-proof-propositions.md`: predicate-form headings, `<DOMAIN>-<n>` IDs, and a
short Lean stub per proposition.

- **Goal**: an unambiguous, Lean-syntax catalog of every proposition we need to prove
  to formally certify the correctness section of Simplex.
- **Scope of this document**: proposition statements only. Proofs and the underlying
  protocol model (`LeanSpec/Simplex/Model.lean`) are out of scope here and tracked as
  follow-ups.
- **Out of scope**: the cryptographic algebra of digital signatures, hash functions,
  and the random-leader oracle. These are stated as `axiom`s under the `SIMP-AX-*`
  prefix, in the same way that `SSZ-7` axiomatizes Merkle-root collision resistance
  in `docs/lean4-proof-propositions.md`.

The intended Lean 4 location for the proofs is
`LeanSpec/Simplex/{Model,Consistency,Liveness}.lean`. These files do not yet exist —
this catalog is the prerequisite that defines what they will contain.

## Approach

### Items per proposition

The proposition statement itself is the **heading** in predicate form. Each proposition
block is composed of:

- **Source**: the blog/paper item that backs the proposition (e.g. "Claim A
  (Consistency)", "Observation A (Liveness)", "Voting Step (§ Full Protocol)").
- **Note** (optional): one-line natural-language description.
- **Sample code**: a Lean 4 stub. The proof body is left as `sorry`:

  ```lean
  theorem foo (s : SimplexState) : P s := by sorry
  ```

  All stubs assume the `LeanSpec.Simplex` namespace and the type/predicate vocabulary
  fixed in §Setup below.

### Proposition ID convention

Format: `SIMP-<DOMAIN>-<number>`. `DOMAIN` is one of:

| Prefix       | Domain                                                 | Lean 4 location (planned)            |
|--------------|--------------------------------------------------------|--------------------------------------|
| `SIMP-CON`   | Consistency (Claims A, B, finalization conclusion)     | `LeanSpec/Simplex/Consistency.lean`  |
| `SIMP-LIV`   | Liveness (Observation A, Claims B, C)                  | `LeanSpec/Simplex/Liveness.lean`     |
| `SIMP-AUX`   | Auxiliary lemmas underpinning both arguments           | `LeanSpec/Simplex/Consistency.lean`  |
| `SIMP-AX`    | Cryptographic / oracle assumptions (declared `axiom`)  | `LeanSpec/Simplex/Model.lean`        |

### Required structural discipline

These rules apply to every stub in the catalog and matter for downstream
formalization:

- All `SIMP-LIV-*` stubs include an explicit `postGST` hypothesis on the entry-time
  variable. Without it, message delivery is not yet δ-bounded and the timing claims
  are simply false; the source text takes this for granted, but the Lean statement
  must be explicit.
- The leader-related stubs (`SIMP-LIV-2`, `SIMP-LIV-3`, `SIMP-LIV-5`) take their
  entry-time premise on `leader h`, **not** on an arbitrary honest player. This
  matches Claim B's exact quantification — a "some honest `p` entered" version is
  strictly weaker because Observation A only delivers `leader h` by `t + δ`, which
  would shift the bounds.
- Stubs that talk about two honest views (`SIMP-CON-3`, `SIMP-CON-5`) use **two
  independent times** `t₁`, `t₂`, matching the "ever sees" / "ever finalizes"
  quantification of Claims A and B.
- Every stub uses the canonical predicate names listed in §Setup. The catalog never
  uses `notarizedFor`, ad-hoc renamings, or alternative spellings.
- All quora are written via `quorumSize n` and `Notarization.signers`. The bare
  expressions `2*n/3`, `⌈2n/3⌉`, and `n/3` do not appear inside any stub.

## Setup

Every stub in this catalog is interpreted in the following context. Anything that
appears inside a stub is on this list; anything that is not on this list does not
appear in any stub.

**Types and base abbreviations.** `Iteration` and `Time` are concrete `Nat` aliases
because the timing claims arithmetize over them.

```lean
namespace LeanSpec.Simplex

opaque Player : Type

abbrev Iteration := Nat
abbrev Time      := Nat

structure Block where
  height  : Iteration
  isDummy : Prop
  -- additional fields (parenthash, txs, …) elided

opaque Vote         : Type
opaque Notarization : Type
opaque View         : Player → Time → Type
```

**Constants and named functions.**

- `n : Nat` — total player count.
- `f : Nat` with `f < n / 3` — Byzantine bound.
- `quorumSize n : Nat := (2 * n + 2) / 3` — canonical `⌈2n/3⌉`.
- `δ Δ GST : Time` — post-GST message delay, round timeout, global stabilization time.
- `leader : Iteration → Player` — the iteration's designated leader (`H*(h) mod n`).
- `dummyBlock : Iteration → Block` — the canonical dummy block of a height, with
  `(dummyBlock h).height = h` and `(dummyBlock h).isDummy`.
- `Notarization.height  : Notarization → Iteration`
- `Notarization.block   : Notarization → Block`
- `Notarization.signers : Notarization → Finset Player` — distinct signers; well-formed
  notarizations satisfy `(N.signers).card ≥ quorumSize n`.
- `Vote.signer    : Vote → Player`
- `Vote.iteration : Vote → Iteration`
- `Vote.block     : Vote → Block`
- `validSignature : Player → Vote → Prop` — used only by `SIMP-AX-1`.

**Predicates** (canonical names; used uniformly by every stub).

- `honest   : Player → Prop`
- `faulty   : Player → Prop`
- `enteredIteration : Player → Iteration → Time → Prop`
- `votedFor         : Player → Iteration → Block → Time → Prop`
- `dummyVoted       : Player → Iteration → Time → Prop`
- `finalized        : Player → Iteration → Block → Time → Prop`
- `notarizedInView  : Player → Block → Time → Prop`
- `postGST          : Time → Prop` with `postGST t ↔ GST ≤ t`.

## Consistency

The Consistency argument has three named claims in the source: Claim A (Quorum
Intersection), Claim B (Finalization Exclusivity), and the Consistency Conclusion.
The propositions below decompose those three claims plus the two voting-rule
preconditions they depend on.

### SIMP-CON-1: An honest player votes for at most one non-dummy block per iteration

- Source: Voting Step (§ Full Protocol Description), simplex.blog/protocol
- Note: An honest player follows the voting rule strictly — within a single iteration
  they sign at most one non-dummy `vote` message.
- Sample code:

  ```lean
  theorem honest_unique_vote
      {p : Player} {h : Iteration} {b b' : Block} {t t' : Time}
      (hp : honest p)
      (hbnd  : ¬ b.isDummy)  (hb'nd : ¬ b'.isDummy)
      (hv  : votedFor p h b  t)
      (hv' : votedFor p h b' t') :
      b = b' := by sorry
  ```

### SIMP-CON-2: An honest player casts dummy-vote XOR finalize per iteration

- Source: Backup/Timeout step + Finalizing Transactions step (§ Full Protocol)
- Note: Within a single iteration, an honest player either contributes to the dummy
  notarization or sends a finalize message — never both. This is the structural
  property that powers Claim B.
- Sample code:

  ```lean
  theorem honest_dummy_xor_finalize
      {p : Player} {h : Iteration} {b : Block} {t t' : Time}
      (hp : honest p)
      (hd : dummyVoted p h t)
      (hf : finalized  p h b t') :
      False := by sorry
  ```

### SIMP-CON-3: No two competing non-dummy blocks of the same height are both notarized

- Source: Claim A — Quorum Intersection (§ Consistency), simplex.blog/protocol
- Note: The "ever sees" quantifier in Claim A is captured by allowing the two views
  to be observed at independent times `t₁`, `t₂`.
- Sample code:

  ```lean
  theorem no_competing_notarizations
      {h : Iteration} {p q : Player} {t₁ t₂ : Time} {b b' : Block}
      (hp : honest p) (hq : honest q)
      (hbh  : b.height  = h) (hbh' : b'.height = h)
      (hbnd : ¬ b.isDummy)   (hb'nd : ¬ b'.isDummy)
      (hpb  : notarizedInView p b  t₁)
      (hqb' : notarizedInView q b' t₂) :
      b = b' := by sorry
  ```

### SIMP-CON-4: A finalized iteration excludes a dummy-block notarization in any honest view

- Source: Claim B — Finalization Exclusivity (§ Consistency), simplex.blog/protocol
- Note: "The dummy block of height `h`" is the canonical `dummyBlock h` from §Setup,
  so the proposition is well-defined even though `Block.isDummy` alone would not pin
  down a unique block.
- Sample code:

  ```lean
  theorem finalize_excludes_dummy
      {h : Iteration} {p q : Player} {b : Block} {t t' : Time}
      (hp : honest p) (hq : honest q)
      (hf : finalized p h b t)
      (hd : notarizedInView q (dummyBlock h) t') :
      False := by sorry
  ```

### SIMP-CON-5: If two honest players finalize at height h (possibly at different times), they finalize the same block

- Source: Consistency Conclusion (§ Consistency), simplex.blog/protocol
- Note: This is the **pairwise agreement** form of the Consistency Conclusion. The
  source text also says "every honest player finalizes the same block at `h`", but
  that "every honest player will finalize" half is an *eventual finalization* claim
  with a liveness flavour and is carried by `SIMP-LIV-3` / `SIMP-LIV-5` under their
  post-GST and honest-leader premises. This is an explicit scope decision — see the
  catalog "Approach" rules above.
- Sample code:

  ```lean
  theorem finalize_agreement
      {h : Iteration} {p q : Player} {t₁ t₂ : Time} {b b' : Block}
      (hp : honest p) (hq : honest q)
      (hf  : finalized p h b  t₁)
      (hf' : finalized q h b' t₂) :
      b = b' := by sorry
  ```

## Liveness

Every stub here is conditioned on `postGST t` for the entry-time variable, since the
δ-bound on message delivery only holds after global stabilization. The leader-honesty
premise is on `leader h` directly, not on an arbitrary honest player, to mirror
Claim B's quantification.

### SIMP-LIV-1: After GST, entering iteration h propagates to all honest players within δ

- Source: Observation A (§ Liveness), simplex.blog/protocol
- Note: Once one honest player enters iteration `h`, the others learn within one
  message-delivery delay.
- Sample code:

  ```lean
  theorem entry_propagates_in_delta
      {h : Iteration} {t : Time} {p : Player}
      (hgst : postGST t)
      (hp : honest p) (hen : enteredIteration p h t) :
      ∀ q, honest q → enteredIteration q h (t + δ) := by sorry
  ```

### SIMP-LIV-2: After GST, an honest leader's iteration completes within 2δ for all honest players

- Source: Claim B part 1 (§ Liveness), simplex.blog/protocol
- Note: The premise is on `leader h`'s entry time, not "some honest player's", so
  that the `2δ` bound is tight (otherwise Observation A only gives the leader by
  `t + δ`).
- Sample code:

  ```lean
  theorem honest_leader_advances
      {h : Iteration} {t : Time}
      (hgst  : postGST t)
      (hlead : honest (leader h))
      (hen   : enteredIteration (leader h) h t) :
      ∀ q, honest q → enteredIteration q (h + 1) (t + 2 * δ) := by sorry
  ```

### SIMP-LIV-3: After GST, an honest leader's proposed block is finalized within 3δ for all honest players

- Source: Claim B part 2 (§ Liveness), simplex.blog/protocol
- Note: Strictly stronger than `SIMP-LIV-2`. The same leader entry premise; the
  conclusion is finalization (not just iteration advance) at the leader's proposal.
- Sample code:

  ```lean
  theorem honest_leader_finalizes
      {h : Iteration} {t : Time}
      (hgst  : postGST t)
      (hlead : honest (leader h))
      (hen   : enteredIteration (leader h) h t) :
      ∃ b : Block,
        b.height = h ∧ ¬ b.isDummy ∧
        ∀ q, honest q → finalized q h b (t + 3 * δ) := by sorry
  ```

### SIMP-LIV-4: After GST, every honest player enters iteration h+1 within 3Δ + δ even if the leader is faulty

- Source: Claim C (§ Liveness), simplex.blog/protocol
- Note: This is the resilience clause — progress is preserved (if no finalization)
  even when `leader h` is faulty, paid for by an extra `3Δ` timeout cost.
- Sample code:

  ```lean
  theorem faulty_leader_advances
      {h : Iteration} {t : Time}
      (hgst : postGST t)
      (hen  : ∀ p, honest p → enteredIteration p h t) :
      ∀ q, honest q → enteredIteration q (h + 1) (t + 3 * Δ + δ) := by sorry
  ```

### SIMP-LIV-5: After GST, conditional on iteration h having an honest leader, all honest players finalize a block at h within 3δ

- Source: Liveness corollary of `SIMP-LIV-3` together with `SIMP-LIV-1`
- Note: The conditional-finalization companion to `SIMP-CON-5`'s pairwise-agreement
  scope decision. An unconditional "transactions are eventually finalized" theorem
  is **not** in this catalog: that depends on `SIMP-AX-3` (uniform random leader
  election) plus continued proposal availability, neither of which is a deterministic
  protocol property.
- Sample code:

  ```lean
  theorem honest_leader_universal_finalization
      {h : Iteration} {t : Time}
      (hgst  : postGST t)
      (hlead : honest (leader h))
      (hen   : ∃ p, honest p ∧ enteredIteration p h t) :
      ∃ b : Block,
        b.height = h ∧ ¬ b.isDummy ∧
        ∀ q, honest q → finalized q h b (t + 3 * δ) := by sorry
  ```

## Auxiliary

These are the lemmas that the Consistency and Liveness proofs call directly. They
are not user-visible correctness claims, but they must be in place before any of
`SIMP-CON-3`, `SIMP-CON-4`, `SIMP-CON-5` can be discharged.

### SIMP-AUX-1: Two `quorumSize n` quora over n players intersect in more than f players

- Source: Standard Byzantine quorum-intersection counting, used implicitly by Claim A
- Note: The single arithmetic fact that powers the consistency argument. Stated only
  in terms of `quorumSize n` and `f`, so the catalog has exactly one identity to
  discharge for the various `2n/3` / `⌈2n/3⌉` / `n/3` phrasings in the source.
- Sample code:

  ```lean
  theorem quorum_intersection
      (S T : Finset Player)
      (hS : S.card ≥ quorumSize n) (hT : T.card ≥ quorumSize n)
      (hS_le : S.card ≤ n)         (hT_le : T.card ≤ n)
      (hf    : f < n / 3) :
      (S ∩ T).card > f := by sorry
  ```

### SIMP-AUX-2: A notarization contains more than f honest signers

- Source: `SIMP-AUX-1` applied to the honest population, plus `f < n / 3`
- Note: Specializes the intersection lemma to the case where one of the quora is the
  honest set. This is what unblocks "some honest player must have signed".
- Sample code:

  ```lean
  theorem notarization_has_honest_signer
      (N : Notarization)
      (hN : (N.signers).card ≥ quorumSize n)
      (hf : f < n / 3) :
      ((N.signers).filter honest).card > f := by sorry
  ```

### SIMP-AUX-3: A view monotonically grows over time

- Source: View definition (§ Setup of the source) — no message is forgotten.
- Note: A "monotonicity" lemma that lets a fact observed at `t` be reused at any
  later `t' ≥ t`.
- Sample code:

  ```lean
  theorem view_monotone
      {p : Player} {b : Block} {t t' : Time}
      (hle : t ≤ t')
      (hb  : notarizedInView p b t) :
      notarizedInView p b t' := by sorry
  ```

### SIMP-AUX-4: A finalize message at height h implies a notarization for the same block at h

- Source: Finalizing Transactions step (§ Full Protocol Description) — finalize is
  sent only after seeing a notarized block.
- Note: Bridges the `finalized` predicate to the `notarizedInView` predicate, which
  is what `SIMP-CON-4` and `SIMP-CON-5` need.
- Sample code:

  ```lean
  theorem finalize_implies_notarized
      {p : Player} {h : Iteration} {b : Block} {t : Time}
      (hp : honest p)
      (hf : finalized p h b t) :
      notarizedInView p b t := by sorry
  ```

## Cryptographic and oracle assumptions

Mirroring `SSZ-7` in `docs/lean4-proof-propositions.md`, these are declared as
`axiom`s rather than theorems. The algebraic content lives in Arklib (or its
analogue); this catalog only records the call-site axioms.

### SIMP-AX-1: Digital signature unforgeability

- Source: Digital Signatures (§ Setup), simplex.blog/protocol
- Note: A valid signature on a vote can only be produced by the player whose key
  pair it claims to come from.
- Sample code:

  ```lean
  axiom signatureUnforgeability
      {p : Player} {v : Vote} :
      validSignature p v → v.signer = p
  ```

### SIMP-AX-2: Hash collision resistance

- Source: Data Structures (§ Setup), simplex.blog/protocol
- Note: Restated for blocks. The same axiom underpins Merkle-tree integrity in
  `SSZ-7`; here it is the statement that a notarization's referenced parent hash
  uniquely identifies its parent block.
- Sample code:

  ```lean
  opaque blockHash : Block → ByteArray

  axiom blockHash_collisionResistance
      {a b : Block} :
      blockHash a = blockHash b → a = b
  ```

### SIMP-AX-3: The random leader oracle is uniformly distributed and independent across iterations

- Source: High-Level Structure — Leader Selection (§ Full Protocol), simplex.blog/protocol
- Note: This is the assumption that powers the unconditional "eventually some
  honest leader is elected" half of liveness. It is intentionally **not** a
  precondition of any `SIMP-LIV-*` theorem in this catalog (those are
  honest-leader-conditional). When a future fairness theorem is added, it will
  cite this axiom directly.
- Sample code:

  ```lean
  axiom leaderOracle_uniform
      (h : Iteration) (p : Player) :
      -- Probability that leader h = p, modeled here as an opaque
      -- predicate `leaderProbability h p = 1 / n`.
      True
  -- Note: a precise probabilistic formalization belongs in a probability-theory
  -- layer (Mathlib's `MeasureTheory` / `ProbabilityTheory`) and is deferred.
  ```
