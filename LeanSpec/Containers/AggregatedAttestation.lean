/-
  AggregatedAttestation container.

  Mirrors `src/lean_spec/subspecs/containers/attestation/attestation.py`. This
  is the only container in scope with a variable-size field, so the encoding
  layout matters: the field declaration order is `aggregationBits` (variable)
  then `data` (fixed). Per SSZ container rules the encoding is

  1. Fixed-size header (occupies positions `[0, fixedHeaderSize)`):
     - At the slot for `aggregationBits`: a 4-byte little-endian offset.
     - At the slot for `data`: the 128-byte body of `data` inline.
  2. After the header, the body of `aggregationBits` follows.

  `fixedHeaderSize = 4 (offset of aggregationBits) + 128 (body of data) = 132`.
  The single offset emitted at position 0 therefore equals `132`.
-/

import LeanSpec.Containers.AttestationData
import LeanSpec.Codec.Endian

namespace LeanSpec.Containers

open LeanSpec
open LeanSpec.Types
open LeanSpec.Codec.Endian

/-- Aggregated participation bits paired with the shared attestation data. -/
structure AggregatedAttestation where
  aggregationBits : AggregationBits
  data            : AttestationData
  deriving BEq, Inhabited

namespace AggregatedAttestation

/-- Size of the fixed-size prefix: one 4-byte offset slot + the inline data body. -/
def fixedHeaderSize : Nat := 4 + AttestationData.byteLength

instance : SSZType AggregatedAttestation where
  isFixedSize := false
  fixedByteLength := 0
  serialize x out :=
    let body := SSZType.serialize x.aggregationBits ByteArray.empty
    let withOffset := pushU32LE out (UInt32.ofNat fixedHeaderSize)
    let withData := SSZType.serialize x.data withOffset
    withData ++ body
  deserialize bs off sz :=
    if sz < fixedHeaderSize then
      .error (.underflow fixedHeaderSize sz)
    else if off + sz > bs.size then
      .error (.underflow sz (bs.size - off))
    else
      let firstOffset := (readU32LE bs off).toNat
      if firstOffset ≠ fixedHeaderSize then
        .error (.offsetTableMisaligned firstOffset fixedHeaderSize)
      else
        match SSZType.deserialize (T := AttestationData) bs (off + 4) AttestationData.byteLength with
        | .error e => .error e
        | .ok data =>
          let bitsScope := sz - fixedHeaderSize
          match SSZType.deserialize (T := AggregationBits) bs (off + fixedHeaderSize) bitsScope with
          | .error e => .error e
          | .ok bits => .ok ⟨bits, data⟩

end AggregatedAttestation
end LeanSpec.Containers
