/-
  SSZ-wide numeric constants. Mirrors `src/lean_spec/subspecs/ssz/constants.py`.
-/

namespace LeanSpec.SSZ.Constants

/-- Number of bytes per Merkle chunk (always 32 in SSZ). -/
def BYTES_PER_CHUNK : Nat := 32

/-- Number of bits packed into a single chunk. -/
def BITS_PER_CHUNK : Nat := 256

/-- Width of the offset entry in a variable-length container or list (uint32 LE). -/
def BYTES_PER_LENGTH_OFFSET : Nat := 4

end LeanSpec.SSZ.Constants
