/-
Chain configuration committed into the consensus state.

Mirrors `src/lean_spec/spec/forks/lstar/containers/genesis.py` in leanSpec:
  - `class GenesisConfig(Container)` — carries `genesis_time`.

Supports the ST-* propositions from `docs/lean4-proof-propositions.md`
(no theorems in this file).
-/

import LeanSpec.Aliases

namespace LeanSpec.Forks.Lstar

/-- Chain configuration committed into consensus state. -/
structure GenesisConfig where
  genesisTime : SSZ.Uint64
  deriving Inhabited, BEq, Repr

end LeanSpec.Forks.Lstar
