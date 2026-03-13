section

open String (Iterator)

abbrev InputReader := EStateM Unit Iterator

partial def skipWhiteSpacesHelper (iter : Iterator) : Iterator :=
  if iter.atEnd || !iter.curr.isWhitespace then
    iter
  else
    skipWhiteSpacesHelper iter.next

def skipWhiteSpaces : InputReader Unit :=
  EStateM.modifyGet fun iter => ⟨(), skipWhiteSpacesHelper iter⟩

partial def readNatHelper (num : Nat) (iter : Iterator) : Nat × Iterator :=
  if iter.atEnd || !iter.curr.isDigit then
    (num, iter)
  else
    let digit := iter.curr.toNat - 48
    readNatHelper (num * 10 + digit) iter.next

def readNat : InputReader Nat := do
  skipWhiteSpaces
  let iter ← EStateM.get
  if iter.atEnd || !iter.curr.isDigit then
    EStateM.throw ()
  let num ← EStateM.modifyGet (readNatHelper 0)
  return num

def readFin (n : Nat) : InputReader (Fin n) := do
  let f ← readNat
  if cond : f < n then
    return ⟨f, cond⟩
  else
    EStateM.throw ()

end

def readProblemInput : InputReader (Nat × Nat) :=
  return ((← readNat), (← readNat))

-- Template: ABC086A
def main : IO Unit := do
  let stdin ← IO.getStdin
  let instr ← stdin.readToEnd
  match readProblemInput.run instr.iter with
  | .error _ _ => unreachable!
  | .ok input _ => do
    let (a, b) := input
    if (a * b) % 2 == 0 then
      IO.println "Even"
    else
      IO.println "Odd"
