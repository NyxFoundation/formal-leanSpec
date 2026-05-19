/-
SSZ Uint64 primitive.

Mirrors `src/lean_spec/types/uint.py` in leanSpec:
  - `class Uint64(BaseUint)` with `BITS = 64`
  - `__new__` enforces `0 <= value <= 2^64 - 1`
  - `encode_bytes`: `value.to_bytes(BITS // 8, byteorder="little")` (8 bytes LE)
  - `decode_bytes`: requires `len(data) == 8`, then `int.from_bytes(data, "little")`

In Lean we reuse the core `UInt64` type, whose internal representation
`Fin UInt64.size` (with `UInt64.size = 2 ^ 64`) coincides with the
Python-side range invariant. Decode failures are modeled as `Option.none`.

Proves SSZ-2 and SSZ-3 from `docs/lean4-proof-propositions.md`:
  - SSZ-2: `∀ v : Uint64, v.toNat < 2 ^ 64`
  - SSZ-3: `∀ v : Uint64, Uint64.decode (Uint64.encode v) = some v`
           and `(Uint64.encode v).size = 8`.
-/

namespace LeanSpec.SSZ

abbrev Uint64 := UInt64

namespace Uint64

theorem range (v : Uint64) : v.toNat < 2 ^ 64 :=
  v.toNat_lt

/-- `encodeNat n k` writes `n` as `k` little-endian bytes (least-significant first). -/
def encodeNat (n : Nat) : Nat → List UInt8
  | 0     => []
  | k + 1 => UInt8.ofNat (n % 256) :: encodeNat (n / 256) k

/-- `decodeNat bs` reads a little-endian byte list as a natural number. -/
def decodeNat : List UInt8 → Nat
  | []      => 0
  | b :: bs => b.toNat + 256 * decodeNat bs

/-- SSZ 8-byte little-endian encoding of a `Uint64`. -/
def encode (v : Uint64) : ByteArray :=
  ⟨(encodeNat v.toNat 8).toArray⟩

/-- SSZ 8-byte little-endian decoder. `none` if the input is not exactly 8 bytes. -/
def decode (bs : ByteArray) : Option Uint64 :=
  if bs.size = 8 then
    some (UInt64.ofNat (decodeNat bs.data.toList))
  else
    none

private theorem encodeNat_length (n k : Nat) : (encodeNat n k).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [encodeNat, ih]

theorem encode_size (v : Uint64) : (encode v).size = 8 := by
  show (encodeNat v.toNat 8).toArray.size = 8
  rw [List.size_toArray, encodeNat_length]

/--
Base-256 step lemma: `n mod (256·m)` splits into the bottom byte and the next
`m` digits of `n / 256`. The base-256 positional reconstruction is built on top
of this single step.
-/
private theorem mod_step (n m : Nat) :
    n % (256 * m) = n % 256 + 256 * ((n / 256) % m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp; omega
  have hr_lt : n % 256 < 256 := Nat.mod_lt n (by decide)
  have hqm : (n / 256) % m < m := Nat.mod_lt _ hm
  have hr_lt_M : n % 256 < 256 * m := by
    have : 256 ≤ 256 * m := Nat.le_mul_of_pos_right 256 hm
    omega
  have hbound : 256 * ((n / 256) % m) + n % 256 < 256 * m := by
    have h_step : 256 * ((n / 256) % m) + 256 ≤ 256 * m := by
      calc 256 * ((n / 256) % m) + 256
          = 256 * ((n / 256) % m + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ ≤ 256 * m := Nat.mul_le_mul_left 256 hqm
    omega
  have h_lhs : n % (256 * m) = (256 * (n / 256) + n % 256) % (256 * m) := by
    conv =>
      lhs
      rw [← Nat.div_add_mod n 256]
  rw [h_lhs]
  calc (256 * (n / 256) + n % 256) % (256 * m)
      = ((256 * (n / 256)) % (256 * m) + (n % 256) % (256 * m)) % (256 * m) :=
          Nat.add_mod _ _ _
    _ = (256 * ((n / 256) % m) + (n % 256) % (256 * m)) % (256 * m) := by
          rw [Nat.mul_mod_mul_left]
    _ = (256 * ((n / 256) % m) + n % 256) % (256 * m) := by
          rw [Nat.mod_eq_of_lt hr_lt_M]
    _ = 256 * ((n / 256) % m) + n % 256 := Nat.mod_eq_of_lt hbound
    _ = n % 256 + 256 * ((n / 256) % m) := Nat.add_comm _ _

private theorem decodeNat_encodeNat (n k : Nat) :
    decodeNat (encodeNat n k) = n % 256 ^ k := by
  induction k generalizing n with
  | zero =>
    show decodeNat [] = n % 1
    simp [decodeNat, Nat.mod_one]
  | succ k ih =>
    show (UInt8.ofNat (n % 256)).toNat + 256 * decodeNat (encodeNat (n / 256) k)
        = n % 256 ^ (k + 1)
    rw [ih]
    have h_uint8 : (UInt8.ofNat (n % 256)).toNat = n % 256 :=
      UInt8.toNat_ofNat_of_lt' (Nat.mod_lt n (by decide))
    rw [h_uint8, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, mod_step]

theorem decode_encode (v : Uint64) : decode (encode v) = some v := by
  have h_size : (encode v).size = 8 := encode_size v
  unfold decode
  rw [if_pos h_size]
  congr 1
  show UInt64.ofNat (decodeNat (encodeNat v.toNat 8).toArray.toList) = v
  rw [List.toList_toArray, decodeNat_encodeNat]
  have h_pow : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  rw [h_pow, Nat.mod_eq_of_lt v.toNat_lt]
  exact UInt64.ofNat_toNat

end Uint64
end LeanSpec.SSZ
