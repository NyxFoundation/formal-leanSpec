/-
Networking configuration constants.

Mirrors `src/lean_spec/node/networking/config.py` in leanSpec. Only the
constants consumed by the modeled req/resp logic are declared.

Supports the NET-* propositions from `docs/lean4-proof-propositions.md`
(no theorems in this file).
-/

namespace LeanSpec.Networking

/-- Maximum number of blocks one `BlocksByRange` request may ask for
(`MAX_REQUEST_BLOCKS`, an `int` upstream). -/
def MAX_REQUEST_BLOCKS : Nat := 2 ^ 10

/-- Maximum size of an uncompressed req/resp payload in bytes
(`MAX_PAYLOAD_SIZE`, an `int` upstream: 10 MiB). -/
def MAX_PAYLOAD_SIZE : Nat := 10 * 1024 * 1024

/-- Depth of the sliding history window a server must keep answerable
for `BlocksByRange` (`MIN_SLOTS_FOR_BLOCK_REQUESTS`, an `int`
upstream). -/
def MIN_SLOTS_FOR_BLOCK_REQUESTS : Nat := 3600

end LeanSpec.Networking
