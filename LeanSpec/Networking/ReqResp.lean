/-
Req/resp protocol: the BlocksByRange handler.

Mirrors `src/lean_spec/node/networking/reqresp/` in leanSpec:
  - `ResponseCode` (`codec.py`) — the first byte of every response:
    success, or one of three failure classes.
  - `BlocksByRangeRequest` (`message.py`) — a start slot and a count.
  - `RequestHandler.handle_blocks_by_range` (`handler.py`) — checks in
    upstream order: server misconfiguration (no block lookup), a
    malformed count (zero, or above `MAX_REQUEST_BLOCKS`), a missing
    current-slot source, a start slot below the sliding history window
    (`max(0, current_slot - MIN_SLOTS_FOR_BLOCK_REQUESTS)`), then
    streams the canonical block of each slot in the range, silently
    skipping empty slots per spec.

The node runtime enters as data: the `block_by_slot_lookup` callback is
the `lookup?` parameter (`none` mirrors the unconfigured server), the
nullary `current_slot_lookup` callback is the `currentSlot?` value, and
the async stream becomes the returned list, in slot order. A lookup
that raises is logged and skipped upstream; the total model has no
raising lookups, so the skip needs no counterpart. `start_slot + i`
wraps in `UInt64` where Python's checked `Slot` would raise — a
divergence only past slot `2^64 - count`.

Proves NET-1 from `docs/lean4-proof-propositions.md`:
  - NET-1: a `BlocksByRange` response never exceeds the bound — at most
    one block per requested slot, and the request is only served when
    its count is within `MAX_REQUEST_BLOCKS`
    (`blocks_by_range_bounded`: `resp.length ≤ min count
    MAX_REQUEST_BLOCKS`).
-/

import LeanSpec.Forks.Lstar.Containers.Block
import LeanSpec.Networking.Config

namespace LeanSpec.Networking

open LeanSpec.Forks.Lstar (SignedBlock)

/-- Response codes for req/resp protocol messages (`ResponseCode`):
the first byte of every response indicates success or the failure
class. -/
inductive ResponseCode where
  /-- Request completed successfully; the payload is the response. -/
  | success
  /-- Request was malformed or violated protocol rules. -/
  | invalidRequest
  /-- Server encountered an internal error processing the request. -/
  | serverError
  /-- Requested resource is not available. -/
  | resourceUnavailable
  deriving Repr, DecidableEq, Inhabited

/-- A request for one or more blocks by their slot numbers
(`BlocksByRangeRequest`), used to recover recent or missing blocks
from a peer. -/
structure BlocksByRangeRequest where
  /-- The starting slot of the range (inclusive). -/
  startSlot : Slot
  /-- The number of blocks to request (at most `MAX_REQUEST_BLOCKS`). -/
  count : SSZ.Uint64
  deriving Inhabited, Repr

/-- Handle an incoming `BlocksByRange` request
(`handle_blocks_by_range`), as the pure core of the streaming handler:
the checks run in upstream order and the streamed blocks come back as
a list in slot order, empty slots silently skipped. -/
def handleBlocksByRange (lookup? : Option (Slot → Option SignedBlock))
    (currentSlot? : Option Slot) (req : BlocksByRangeRequest) :
    Except ResponseCode (List SignedBlock) :=
  -- Reject when no block lookup is configured (server misconfiguration).
  match lookup? with
  | none => .error .serverError
  | some lookup =>
    -- A count of zero is INVALID_REQUEST in modern forks, as is a count
    -- above the limit.
    if req.count.toNat = 0 ∨ MAX_REQUEST_BLOCKS < req.count.toNat then
      .error .invalidRequest
    else
      -- Without a current-slot source the window cannot be placed.
      match currentSlot? with
      | none => .error .serverError
      | some currentSlot =>
        -- Sliding window: max(0, current_slot - MIN_SLOTS) to current.
        let windowFloor : Slot :=
          if MIN_SLOTS_FOR_BLOCK_REQUESTS ≤ currentSlot.toNat then
            UInt64.ofNat (currentSlot.toNat - MIN_SLOTS_FOR_BLOCK_REQUESTS)
          else 0
        if req.startSlot < windowFloor then
          .error .resourceUnavailable
        else
          -- Stream blocks in slot order; the lookup returns
          -- canonical-only blocks and `none` for empty slots.
          .ok ((List.range req.count.toNat).filterMap fun i =>
            lookup (UInt64.ofNat (req.startSlot.toNat + i)))

/-- At most one element per visited index, capped by the protocol
limit. -/
private theorem filterMap_range_le_min {α : Type} (f : Nat → Option α)
    (n : Nat) (hn : n ≤ MAX_REQUEST_BLOCKS) :
    ((List.range n).filterMap f).length ≤ min n MAX_REQUEST_BLOCKS := by
  have hle : ((List.range n).filterMap f).length ≤ n := by
    simpa using List.length_filterMap_le f (List.range n)
  exact Nat.le_min.mpr ⟨hle, Nat.le_trans hle hn⟩

/-- NET-1: a `BlocksByRange` response never exceeds the requested count
nor the protocol cap — the loop visits each requested slot once and
sends at most one block for it, and a count above `MAX_REQUEST_BLOCKS`
is rejected before any block is looked up. -/
theorem blocks_by_range_bounded
    (lookup? : Option (Slot → Option SignedBlock))
    (currentSlot? : Option Slot) (req : BlocksByRangeRequest)
    (resp : List SignedBlock)
    (h : handleBlocksByRange lookup? currentSlot? req = .ok resp) :
    resp.length ≤ min req.count.toNat MAX_REQUEST_BLOCKS := by
  unfold handleBlocksByRange at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next hcount =>
      have hmax : req.count.toNat ≤ MAX_REQUEST_BLOCKS :=
        Nat.le_of_not_lt fun hc => hcount (Or.inr hc)
      split at h
      · simp at h
      · dsimp only at h
        split at h
        · split at h
          · simp at h
          · injection h with h'
            subst h'
            exact filterMap_range_le_min _ _ hmax
        · split at h
          · simp at h
          · injection h with h'
            subst h'
            exact filterMap_range_le_min _ _ hmax

end LeanSpec.Networking
