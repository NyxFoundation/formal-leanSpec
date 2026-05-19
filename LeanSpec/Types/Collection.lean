/-
  SSZ collection types.

  Mirrors `src/lean_spec/types/collections.py`:

  - `SSZVector T n`     : exactly `n` elements of `T`.
  - `SSZList   T limit` : 0..`limit` elements of `T`.

  Encoding splits into two cases per the SSZ specification:

  - Fixed-size element: simply concatenate every element's encoding.

  - Variable-size element: emit a 4-byte little-endian offset for each
    element first (the offset table), then the elements' encodings.
    Decoding validates that offsets are monotonically non-decreasing,
    that the first offset equals `numElements * 4`, and that the final
    offset stays within scope.

  In-memory representation is `Array T`; the well-formedness invariants
  (`data.size = n` for vector, `data.size ≤ limit` for list) are not
  encoded in the type. The deserializer always produces values that
  satisfy them, and the spec layer establishes them at construction.
-/

import LeanSpec.Types.Base
import LeanSpec.Codec.Endian
import LeanSpec.SSZ.Constants

namespace LeanSpec.Types

open LeanSpec.Codec.Endian
open LeanSpec.SSZ.Constants

/-- Size in bytes of a single offset table entry. -/
@[inline] def OFFSET_BYTES : Nat := BYTES_PER_LENGTH_OFFSET

/-- Append the encoding of every element in `data` to `out`, given that all
    elements are fixed-size with `SSZType.serialize`. -/
def serializeFixedElems {T : Type} [SSZType T] (data : Array T) (out : ByteArray) : ByteArray :=
  data.foldl (fun acc elem => SSZType.serialize elem acc) out

/-- Append the encoding of every element in `data` to `out`, when elements are
    variable-size. Emits an offset table of `data.size * 4` bytes, then the
    concatenated element bodies. -/
def serializeVariableElems {T : Type} [SSZType T] (data : Array T) (out : ByteArray) : ByteArray := Id.run do
  let bodies : Array ByteArray := data.map (fun e => SSZType.serialize e ByteArray.empty)
  let n := bodies.size
  let mut acc := out
  let mut cursor : Nat := n * OFFSET_BYTES
  for i in [0:n] do
    acc := pushU32LE acc (UInt32.ofNat cursor)
    cursor := cursor + bodies[i]!.size
  for body in bodies do
    acc := acc ++ body
  return acc

/-- Read `n` little-endian uint32 offsets starting at `off`. -/
def readOffsets (bs : ByteArray) (off n : Nat) : Array Nat := Id.run do
  let mut acc : Array Nat := Array.mkEmpty n
  for i in [0:n] do
    acc := acc.push (readU32LE bs (off + i * OFFSET_BYTES)).toNat
  return acc

/-- Decode `n` fixed-size elements from `bs[off : off + n * elemSize]`. -/
def deserializeFixedElems {T : Type} [SSZType T]
    (bs : ByteArray) (off n elemSize : Nat) : SSZ.Result (Array T) :=
  let rec loop (i : Nat) (acc : Array T) : SSZ.Result (Array T) :=
    if i ≥ n then .ok acc
    else
      match SSZType.deserialize bs (off + i * elemSize) elemSize with
      | .ok v => loop (i + 1) (acc.push v)
      | .error e => .error e
  termination_by n - i
  decreasing_by all_goals (rename_i hne; omega)
  loop 0 (Array.mkEmpty n)

/-- Decode `n` variable-size elements given offsets `[o₀, o₁, …, oₙ₋₁]` and the
    overall scope `sz`. Each element occupies `bs[off + oᵢ : off + oᵢ₊₁]` for
    `i < n - 1`, and the last element occupies `bs[off + oₙ₋₁ : off + sz]`. -/
def deserializeVariableElems {T : Type} [SSZType T]
    (bs : ByteArray) (off sz : Nat) (offsets : Array Nat) : SSZ.Result (Array T) :=
  let n := offsets.size
  let rec loop (i : Nat) (acc : Array T) : SSZ.Result (Array T) :=
    if i ≥ n then .ok acc
    else
      let start := offsets[i]!
      let stop := if i + 1 = n then sz else offsets[i + 1]!
      if stop < start then .error .offsetNotMonotone
      else
        match SSZType.deserialize bs (off + start) (stop - start) with
        | .ok v => loop (i + 1) (acc.push v)
        | .error e => .error e
  termination_by n - i
  decreasing_by all_goals omega
  loop 0 (Array.mkEmpty n)

/-- Validate an offset table read from `bs`: first offset = `n * 4`, monotone
    non-decreasing, final offset ≤ `sz`. -/
def validateOffsets (offsets : Array Nat) (sz : Nat) : SSZ.Result Unit :=
  let n := offsets.size
  if n = 0 then .ok ()
  else
    let first := offsets[0]!
    let expected := n * OFFSET_BYTES
    if first ≠ expected then
      .error (.offsetTableMisaligned first expected)
    else
      let rec check (i : Nat) : SSZ.Result Unit :=
        if h : i + 1 ≥ n then
          if offsets[n - 1]! > sz then
            .error (.offsetOutOfRange offsets[n - 1]! sz)
          else .ok ()
        else if offsets[i]! > offsets[i + 1]! then
          .error .offsetNotMonotone
        else check (i + 1)
      termination_by n - i
      decreasing_by all_goals omega
      check 0

/-- Fixed-length vector of SSZ-typed elements. -/
structure SSZVector (T : Type) (n : Nat) where
  data : Array T
  deriving Inhabited

namespace SSZVector

variable {T : Type} [SSZType T] {n : Nat}

instance [BEq T] : BEq (SSZVector T n) where
  beq a b := a.data == b.data

instance : SSZType (SSZVector T n) where
  isFixedSize := SSZType.isFixedSize T
  fixedByteLength :=
    if SSZType.isFixedSize T then n * SSZType.fixedByteLength T else 0
  serialize x out :=
    if SSZType.isFixedSize T then
      serializeFixedElems x.data out
    else
      serializeVariableElems x.data out
  deserialize bs off sz :=
    if SSZType.isFixedSize T then
      let elemSize := SSZType.fixedByteLength T
      let expected := n * elemSize
      if sz ≠ expected then
        .error (.sizeMismatch expected sz)
      else if off + sz > bs.size then
        .error (.underflow sz (bs.size - off))
      else
        match deserializeFixedElems (T := T) bs off n elemSize with
        | .ok arr => .ok ⟨arr⟩
        | .error e => .error e
    else
      if n = 0 then
        if sz = 0 then .ok ⟨#[]⟩ else .error (.sizeMismatch 0 sz)
      else if sz < n * OFFSET_BYTES then
        .error (.underflow (n * OFFSET_BYTES) sz)
      else if off + sz > bs.size then
        .error (.underflow sz (bs.size - off))
      else
        let offsets := readOffsets bs off n
        match validateOffsets offsets sz with
        | .error e => .error e
        | .ok _ =>
          match deserializeVariableElems (T := T) bs off sz offsets with
          | .ok arr => .ok ⟨arr⟩
          | .error e => .error e

end SSZVector

/-- Variable-length list of SSZ-typed elements bounded by `limit`. -/
structure SSZList (T : Type) (limit : Nat) where
  data : Array T
  deriving Inhabited

namespace SSZList

variable {T : Type} [SSZType T] {limit : Nat}

instance [BEq T] : BEq (SSZList T limit) where
  beq a b := a.data == b.data

instance : SSZType (SSZList T limit) where
  isFixedSize := false
  fixedByteLength := 0
  serialize x out :=
    if SSZType.isFixedSize T then
      serializeFixedElems x.data out
    else
      serializeVariableElems x.data out
  deserialize bs off sz :=
    if off + sz > bs.size then
      .error (.underflow sz (bs.size - off))
    else if SSZType.isFixedSize T then
      let elemSize := SSZType.fixedByteLength T
      if elemSize = 0 then
        .ok ⟨#[]⟩
      else if sz % elemSize ≠ 0 then
        .error (.malformed "size not multiple of fixed element size")
      else
        let count := sz / elemSize
        if count > limit then
          .error (.tooManyElements limit count)
        else
          match deserializeFixedElems (T := T) bs off count elemSize with
          | .ok arr => .ok ⟨arr⟩
          | .error e => .error e
    else
      -- Variable elements: number of elements is determined by the first offset.
      if sz = 0 then
        .ok ⟨#[]⟩
      else if sz < OFFSET_BYTES then
        .error (.underflow OFFSET_BYTES sz)
      else
        let firstOffset := (readU32LE bs off).toNat
        if firstOffset % OFFSET_BYTES ≠ 0 then
          .error (.malformed "first offset not aligned to 4")
        else
          let count := firstOffset / OFFSET_BYTES
          if count > limit then
            .error (.tooManyElements limit count)
          else if sz < firstOffset then
            .error (.underflow firstOffset sz)
          else
            let offsets := readOffsets bs off count
            match validateOffsets offsets sz with
            | .error e => .error e
            | .ok _ =>
              match deserializeVariableElems (T := T) bs off sz offsets with
              | .ok arr => .ok ⟨arr⟩
              | .error e => .error e

end SSZList

end LeanSpec.Types
