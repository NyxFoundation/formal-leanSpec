import LeanSpec.Crypto.Sha256

namespace LeanSpec.Tests.Unit.Sha256Test

open LeanSpec.Crypto.Sha256

/-- Convert a ByteArray to lowercase hex string. -/
def toHex (bs : ByteArray) : String := Id.run do
  let digits : Array Char :=
    #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let mut s := ""
  for i in [0:bs.size] do
    let b := bs.get! i
    s := s.push digits[(b.toNat / 16)]! |>.push digits[(b.toNat % 16)]!
  return s

/-- Build a ByteArray from a literal byte list. -/
def bytes (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray

/-- Build a ByteArray of `n` repeated 'a'. -/
def repeatA (n : Nat) : ByteArray := Id.run do
  let mut out : ByteArray := ByteArray.empty
  for _ in [0:n] do
    out := out.push 0x61
  return out

/-- NIST FIPS 180-4 vectors. -/
def expectedEmpty : String :=
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

def expectedAbc : String :=
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

def expectedMillionA : String :=
  "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"

def runAll : IO UInt32 := do
  let mut failures : Nat := 0

  let h1 := toHex (sha256 ByteArray.empty)
  if h1 != expectedEmpty then
    IO.eprintln s!"sha256(\"\") = {h1}, expected {expectedEmpty}"
    failures := failures + 1

  let h2 := toHex (sha256 (bytes [0x61, 0x62, 0x63]))
  if h2 != expectedAbc then
    IO.eprintln s!"sha256(\"abc\") = {h2}, expected {expectedAbc}"
    failures := failures + 1

  let h3 := toHex (sha256 (repeatA 1000000))
  if h3 != expectedMillionA then
    IO.eprintln s!"sha256(1M 'a') = {h3}, expected {expectedMillionA}"
    failures := failures + 1

  if failures = 0 then
    IO.println "Sha256Test: 3/3 vectors pass"
    return 0
  else
    return 1

end LeanSpec.Tests.Unit.Sha256Test
