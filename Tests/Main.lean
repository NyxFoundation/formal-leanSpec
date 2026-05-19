import Tests.Unit.Sha256Test

def main : IO UInt32 := do
  let mut rc : UInt32 := 0
  rc := rc + (← LeanSpec.Tests.Unit.Sha256Test.runAll)
  if rc = 0 then
    IO.println "OK"
    return 0
  else
    IO.eprintln s!"FAIL: {rc} test group(s) failed"
    return 1
