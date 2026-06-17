import Std

def ValidFrom : Nat -> List Char -> Prop
  | bal, [] => bal = 0
  | bal, c :: xs =>
      if c = '(' then
        ValidFrom (bal + 1) xs
      else if c = ')' then
        match bal with
        | 0 => False
        | bal + 1 => ValidFrom bal xs
      else
        False

def IsCorrectParenString (xs : List Char) : Prop :=
  xs ≠ [] ∧ ValidFrom 0 xs

def gen : Nat -> Nat -> List (List Char)
  | 0, bal => if bal = 0 then [[]] else []
  | rem + 1, bal =>
      (gen rem (bal + 1)).map (fun xs => '(' :: xs) ++
        if bal = 0 then [] else (gen rem (bal - 1)).map (fun xs => ')' :: xs)

def solve (N : Nat) : List (List Char) :=
  if N = 0 then [] else gen N 0

def printSolution (answer : List (List Char)) : IO Unit := do
  for xs in answer do
    IO.println (String.mk xs)

theorem gen_sound {rem bal : Nat} {xs : List Char} :
    xs ∈ gen rem bal -> xs.length = rem ∧ ValidFrom bal xs := by
  induction rem generalizing bal xs with
  | zero =>
      simp [gen]
      intro hbal hxs
      subst xs
      exact ⟨rfl, by simpa [ValidFrom] using hbal⟩
  | succ rem ih =>
      simp [gen]
      intro h
      cases h with
      | inl hleft =>
          rcases hleft with ⟨ys, hys, rfl⟩
          have got := ih hys
          exact ⟨by simp [got.1], by simpa [ValidFrom] using got.2⟩
      | inr hright =>
          rcases hright with ⟨hbal, ys, hys, rfl⟩
          have got := ih hys
          cases bal with
          | zero =>
              contradiction
          | succ bal =>
              exact ⟨by simp [got.1], by simpa [ValidFrom] using got.2⟩

theorem gen_complete {rem bal : Nat} {xs : List Char} :
    xs.length = rem -> ValidFrom bal xs -> xs ∈ gen rem bal := by
  induction rem generalizing bal xs with
  | zero =>
      intro hlen hvalid
      cases xs with
      | nil =>
          change bal = 0 at hvalid
          simp [gen, hvalid]
      | cons x xs =>
          simp at hlen
  | succ rem ih =>
      intro hlen hvalid
      cases xs with
      | nil =>
          simp at hlen
      | cons x xs =>
          by_cases hxopen : x = '('
          · subst x
            simp [ValidFrom] at hvalid
            have hmem : xs ∈ gen rem (bal + 1) := ih (by simpa using hlen) hvalid
            simp [gen, hmem]
          · by_cases hxclose : x = ')'
            · subst x
              cases bal with
              | zero =>
                  simp [ValidFrom] at hvalid
              | succ bal =>
                  simp [ValidFrom] at hvalid
                  have hmem : xs ∈ gen rem bal := ih (by simpa using hlen) hvalid
                  simp [gen, hmem]
            · simp [ValidFrom, hxopen, hxclose] at hvalid

theorem solve_sound {N : Nat} {xs : List Char} :
    xs ∈ solve N -> xs.length = N ∧ IsCorrectParenString xs := by
  intro hmem
  by_cases hN : N = 0
  · simp [solve, hN] at hmem
  · simp [solve, hN] at hmem
    have got := gen_sound hmem
    exact ⟨got.1, by
      constructor
      · intro hnil
        subst xs
        simp at got
        exact hN got.1.symm
      · exact got.2⟩

theorem solve_complete {N : Nat} {xs : List Char} :
    xs.length = N -> IsCorrectParenString xs -> xs ∈ solve N := by
  intro hlen hcorrect
  by_cases hN : N = 0
  · have hlen0 : xs.length = 0 := by simpa [hN] using hlen
    have : xs = [] := by simpa using hlen0
    exact False.elim (hcorrect.1 this)
  · simp [solve, hN]
    exact gen_complete hlen hcorrect.2

def SolutionIsValid (N : Nat) (answer : List (List Char)) : Prop :=
  (∀ xs, xs ∈ answer -> xs.length = N ∧ IsCorrectParenString xs) ∧
    (∀ xs, xs.length = N -> IsCorrectParenString xs -> xs ∈ answer)

theorem solution_is_valid (N : Nat) : SolutionIsValid N (solve N) := by
  constructor
  · intro xs hmem
    exact solve_sound hmem
  · intro xs hlen hcorrect
    exact solve_complete hlen hcorrect

def readNat (s : String) : Nat :=
  match s.split (fun c => c = ' ' || c = '\n' || c = '\t' || c = '\r') |>.filter (· ≠ "") with
  | token :: _ => token.toNat!
  | [] => 0

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  printSolution (solve (readNat input))
