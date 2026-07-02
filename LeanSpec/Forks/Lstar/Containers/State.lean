/-
Consensus state (minimal).

Mirrors `src/lean_spec/spec/forks/lstar/containers/state.py` in leanSpec:
  - `class State(Container)` — the consensus state.

Only the fields consumed by ST-1 / ST-2 / ST-5 are modeled:
`slot`, `latest_block_header`, `latest_justified`, `latest_finalized`.

Deferred until ST-3 / ST-4 / ST-6 (justification & finalization machinery)
are taken up: `config`, `historical_block_hashes`, `justified_slots`,
`validators`, `justifications_roots`, `justifications_validators`.

Supports the ST-* propositions from `docs/lean4-proof-propositions.md`
(no theorems in this file).
-/

import LeanSpec.Forks.Lstar.Containers.Block

namespace LeanSpec.Forks.Lstar

/-- The consensus state (minimal ST-1 / ST-2 / ST-5 field set). -/
structure State where
  slot : Slot
  latestBlockHeader : BlockHeader
  latestJustified : Checkpoint
  latestFinalized : Checkpoint
  deriving Inhabited, BEq, Repr

end LeanSpec.Forks.Lstar
