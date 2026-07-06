/-
Sync-service state machine.

Mirrors `src/lean_spec/node/sync/states.py` (`SyncState` and its
`accepts_gossip` property) and the transition guard of
`src/lean_spec/node/sync/service.py` (`SyncService._transition_to`):

    IDLE -> SYNCING -> SYNCED
      ^         |         |
      +---------+---------+

  - IDLE: no peers connected, or shutdown requested.
  - SYNCING: active block processing and backfill driven by gossip.
  - SYNCED: caught up to the network finalized slot.

`_transition_to` validates a *requested* move rather than computing the
next state: it rejects self-transitions and the IDLE → SYNCED shortcut
(SYNCING must run before SYNCED is reached) and accepts every other
pair, including any active state falling back to IDLE. Python raises
`ValueError` on a forbidden move; the model returns `none`.

Proves SYNC-1 and SYNC-2 from `docs/lean4-proof-propositions.md`:
  - SYNC-1: the sync FSM only takes the permitted transitions — every
    move the guard accepts lies in the catalog's `canTransitionTo`
    relation (`transition_sound`). Upstream is in fact stricter than
    that relation: it also rejects the idle self-loop the relation's
    `any_to_idle` admits — `transitionTo_ne` records the
    no-self-transition invariant.
  - SYNC-2: gossip is accepted exactly in `SYNCING` and `SYNCED`
    (`accepts_gossip_iff`) — the gate every `on_gossip_*` handler in
    `node/sync/service.py` checks first, so an `IDLE` node never
    processes (or re-forwards) gossip payloads.
-/

namespace LeanSpec.Sync

/-- Three-phase progression for the sync service (`SyncState`). -/
inductive SyncState where
  /-- No peers connected, or shutdown requested. -/
  | idle
  /-- Active block processing and backfill driven by gossip. -/
  | syncing
  /-- Caught up to the network finalized slot. -/
  | synced
  deriving Repr, DecidableEq, Inhabited

namespace SyncState

/-- Whether incoming gossip blocks should be processed in this state
(`accepts_gossip`: membership in `{SYNCING, SYNCED}`). -/
def acceptsGossip : SyncState → Bool
  | .idle => false
  | .syncing => true
  | .synced => true

/-- SYNC-2: gossip is accepted exactly in the two active states —
`SYNCING` (backfill driven by gossip) and `SYNCED` (live following).
An `IDLE` node processes no gossip, so it cannot re-forward stale or
broken payloads. -/
theorem accepts_gossip_iff (st : SyncState) :
    acceptsGossip st = true ↔ st = .syncing ∨ st = .synced := by
  cases st <;> simp [acceptsGossip]

/-- The catalog's permitted-transition relation (SYNC-1): forward
progress `IDLE → SYNCING → SYNCED`, the fall-behind edge
`SYNCED → SYNCING`, and any state back to `IDLE`. -/
inductive canTransitionTo : SyncState → SyncState → Prop where
  | idle_to_syncing : canTransitionTo .idle .syncing
  | syncing_to_synced : canTransitionTo .syncing .synced
  | synced_to_syncing : canTransitionTo .synced .syncing
  | any_to_idle (s : SyncState) : canTransitionTo s .idle

/-- Validate a requested transition (`SyncService._transition_to`):
self-transitions and the `IDLE → SYNCED` shortcut are rejected —
`SYNCING` must run before `SYNCED` is reached — and every other pair is
accepted. -/
def transitionTo (current new : SyncState) : Option SyncState :=
  if new = current ∨ (current = .idle ∧ new = .synced) then none
  else some new

/-- An accepted move echoes the requested state. -/
theorem transitionTo_eq (s n s' : SyncState)
    (h : transitionTo s n = some s') : s' = n := by
  unfold transitionTo at h
  split at h
  · exact absurd h (by simp)
  · exact (Option.some.inj h).symm

/-- SYNC-1: the sync FSM only takes the permitted transitions — every
move the guard accepts lies in the `canTransitionTo` relation. -/
theorem transition_sound (s n s' : SyncState)
    (h : transitionTo s n = some s') :
    s.canTransitionTo s' := by
  have heq := transitionTo_eq s n s' h
  subst heq
  cases s <;> cases s' <;> simp [transitionTo] at h <;> constructor

/-- Upstream is stricter than the catalog relation: an accepted move
never keeps the current state (`canTransitionTo`'s `any_to_idle` admits
the idle self-loop; `_transition_to` rejects it). -/
theorem transitionTo_ne (s n s' : SyncState)
    (h : transitionTo s n = some s') : s' ≠ s := by
  have heq := transitionTo_eq s n s' h
  subst heq
  unfold transitionTo at h
  split at h
  · exact absurd h (by simp)
  · next hcond =>
    intro hc
    exact hcond (.inl hc)

end SyncState
end LeanSpec.Sync
