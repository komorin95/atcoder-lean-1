-- Template
def main : IO Unit := do
  let stdin ← IO.getStdin
  let instr ← stdin.readToEnd
  let intokens := instr.split (·.isWhitespace)
  let a := intokens[0]!.trim.toNat!
  let b := intokens[1]!.trim.toNat!
  if (a * b) % 2 == 0 then
    IO.println "Even"
  else
    IO.println "Odd"
