/-
  Chunking helpers for SSZ merkleisation.
  Mirrors `src/lean_spec/subspecs/ssz/pack.py`.

  `packBytes` and `packBits` both turn a byte / bit stream into a list of
  32-byte chunks, padding the final chunk with zero bytes if needed.
-/

import LeanSpec.SSZ.Constants
import LeanSpec.Types.ByteArray

namespace LeanSpec.SSZ.Pack

open LeanSpec.SSZ.Constants
open LeanSpec.Types

/-- Number of full chunks plus optional partial chunk required for `n` bytes. -/
@[inline] def chunkCount (n : Nat) : Nat := (n + BYTES_PER_CHUNK - 1) / BYTES_PER_CHUNK

/-- Pack `data` into a list of `Bytes32` chunks. The last chunk is right-padded with zeros. -/
def packBytes (data : ByteArray) : Array Bytes32 := Id.run do
  let total := chunkCount data.size
  let mut out : Array Bytes32 := Array.mkEmpty total
  for i in [0:total] do
    let start := i * BYTES_PER_CHUNK
    let stop := min (start + BYTES_PER_CHUNK) data.size
    let mut chunk : ByteArray := data.extract start stop
    while chunk.size < BYTES_PER_CHUNK do
      chunk := chunk.push 0
    out := out.push ⟨chunk⟩
  return out

/-- Pack a bit array LSB-first into 32-byte chunks. -/
def packBits (bits : Array Bool) : Array Bytes32 := Id.run do
  let nBytes : Nat := (bits.size + 7) / 8
  let mut bytes : ByteArray := ByteArray.empty
  for byteIdx in [0:nBytes] do
    let mut b : UInt8 := 0
    for j in [0:8] do
      let bitIdx := byteIdx * 8 + j
      if hLt : bitIdx < bits.size then
        if bits[bitIdx]'hLt then
          b := b ||| ((1 : UInt8) <<< j.toUInt8)
    bytes := bytes.push b
  return packBytes bytes

end LeanSpec.SSZ.Pack
