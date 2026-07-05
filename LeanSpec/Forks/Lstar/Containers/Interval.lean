/-
Interval time unit.

Mirrors `src/lean_spec/spec/forks/lstar/containers/interval.py` in leanSpec:
  - `class Interval(Uint64)` — interval count since genesis.
  - `Interval.from_slot(slot)` — the first interval of the given slot
    (`slot * INTERVALS_PER_SLOT`; slot boundaries fall on exact multiples
    of the interval count).

Python's `Uint64` constructor raises when the product exceeds `2^64 - 1`;
the Lean `UInt64.ofNat` wraps instead. The divergence needs a slot beyond
`2^64 / INTERVALS_PER_SLOT`, far outside any state reachable within the
`Uint64` slot space consumed one slot at a time.

Supports the FC-* propositions from `docs/lean4-proof-propositions.md`
(no theorems in this file).
-/

import LeanSpec.Aliases
import LeanSpec.Forks.Lstar.Config

namespace LeanSpec.Forks.Lstar

/-- Interval count since genesis (`class Interval(Uint64)`). -/
abbrev Interval := SSZ.Uint64

namespace Interval

/-- The interval at a slot's start (`Interval.from_slot`). -/
def fromSlot (slot : Slot) : Interval :=
  UInt64.ofNat (slot.toNat * INTERVALS_PER_SLOT)

end Interval
end LeanSpec.Forks.Lstar
