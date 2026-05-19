/-
  Merkleisation for SSZ.
  Mirrors `src/lean_spec/subspecs/ssz/merkleization.py`.

  The pre-computed zero-hash table covers tree depths up to `MAX_ZERO_HASH_DEPTH`
  (= 64), which is enough to root a tree with up to `2^64` leaves. Trees beyond
  that fall back to recomputation, mirroring the Python behaviour exactly.
-/

import LeanSpec.SSZ.Utils
import LeanSpec.SSZ.Constants
import LeanSpec.Types.ByteArray
import LeanSpec.Codec.Endian

namespace LeanSpec.SSZ.Merkleization

open LeanSpec.SSZ.Utils
open LeanSpec.SSZ.Constants
open LeanSpec.Types
open LeanSpec.Codec.Endian

/-- Maximum depth of the pre-computed zero-hash table. -/
def MAX_ZERO_HASH_DEPTH : Nat := 64

/-- Build the zero-hash table iteratively: each entry is the root of a full
    zero subtree of width `2^i`. -/
def zeroHashes : Array Bytes32 := Id.run do
  let mut acc : Array Bytes32 := #[zeroBytes32]
  for _ in [0 : MAX_ZERO_HASH_DEPTH] do
    let prev := acc[acc.size - 1]!
    acc := acc.push (hashNodes prev prev)
  return acc

/-- Bit length of `n - 1` viewed as a `Nat`. Returns 0 when `n ≤ 1`. -/
def bitLength (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else
    let rec loop (x : Nat) (acc : Nat) : Nat :=
      if x = 0 then acc else loop (x / 2) (acc + 1)
    loop (n - 1) 0

/-- Root of an all-zero subtree of width `widthPow2`, in `O(1)` for the
    common case where the depth fits in the pre-computed table. -/
def zeroTreeRoot (widthPow2 : Nat) : Bytes32 :=
  if widthPow2 ≤ 1 then zeroBytes32
  else
    let depth := bitLength widthPow2
    if depth < zeroHashes.size then zeroHashes[depth]!
    else Id.run do
      let mut h := zeroHashes[zeroHashes.size - 1]!
      for _ in [0 : depth - zeroHashes.size + 1] do
        h := hashNodes h h
      return h

/-- One bottom-up reduction step: pair adjacent nodes, hashing the lone tail
    against a zero subtree of size `subtreeSize`. -/
def reducePairs (level : Array Bytes32) (subtreeSize : Nat) : Array Bytes32 := Id.run do
  let mut next : Array Bytes32 := Array.mkEmpty ((level.size + 1) / 2)
  let mut i : Nat := 0
  while i < level.size do
    let left := level[i]!
    let right := if i + 1 < level.size then level[i + 1]! else zeroTreeRoot subtreeSize
    next := next.push (hashNodes left right)
    i := i + 2
  return next

/-- Compute the Merkle root of `chunks`, optionally padded to `limit` leaves.
    Mirrors `merkleize` in Python down to the empty/limit edge cases. -/
def merkleize (chunks : Array Bytes32) (limit : Option Nat) : Bytes32 :=
  let n := chunks.size
  match limit with
  | none =>
    if n = 0 then zeroBytes32
    else
      let width := getPowerOfTwoCeil n
      if width = 1 then chunks[0]!
      else Id.run do
        let mut level := chunks
        let mut subtreeSize : Nat := 1
        while subtreeSize < width do
          level := reducePairs level subtreeSize
          subtreeSize := subtreeSize * 2
        return level[0]!
  | some lim =>
    if n = 0 then zeroTreeRoot (getPowerOfTwoCeil lim)
    else if lim < n then zeroBytes32  -- caller should pre-validate; treat as zero
    else
      let width := getPowerOfTwoCeil lim
      if width = 1 then chunks[0]!
      else Id.run do
        let mut level := chunks
        let mut subtreeSize : Nat := 1
        while subtreeSize < width do
          level := reducePairs level subtreeSize
          subtreeSize := subtreeSize * 2
        return level[0]!

/-- 32-byte little-endian encoding of a non-negative `Nat`, padded with zero bytes. -/
def natToBytes32LE (x : Nat) : Bytes32 := Id.run do
  let mut out : ByteArray := ByteArray.empty
  let mut v : Nat := x
  for _ in [0:32] do
    out := out.push (UInt8.ofNat (v % 256))
    v := v / 256
  return ⟨out⟩

/-- Mix a non-negative integer length into a Merkle root. -/
def mixInLength (root : Bytes32) (length : Nat) : Bytes32 :=
  hashNodes root (natToBytes32LE length)

/-- Mix a non-negative integer selector (e.g. union tag) into a Merkle root. -/
def mixInSelector (root : Bytes32) (selector : Nat) : Bytes32 :=
  hashNodes root (natToBytes32LE selector)

end LeanSpec.SSZ.Merkleization
