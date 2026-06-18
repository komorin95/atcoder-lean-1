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

theorem validFrom_decomposition :
    xs ≠ [] -> ValidFrom 0 xs ->
    ∃ ys zs,
    (ValidFrom 0 ys ∧ ValidFrom 0 zs ∧ xs = '(' :: ys ++ [')'] ++ zs) := sorry

inductive CorrectParenString : List Char -> Prop
  | unit : CorrectParenString ['(', ')']
  | wrap {s : List Char} :
      CorrectParenString s -> CorrectParenString ('(' :: s ++ [')'])
  | concat {s t : List Char} :
      CorrectParenString s -> CorrectParenString t -> CorrectParenString (s ++ t)

def IsCorrectParenString (xs : List Char) : Prop :=
  CorrectParenString xs

def InternalCorrectParenString (xs : List Char) : Prop :=
  xs ≠ [] ∧ ValidFrom 0 xs

theorem validFrom_zero_correct {xs : List Char} :
  xs ≠ [] -> ValidFrom 0 xs -> CorrectParenString xs := sorry

def Run : Nat -> List Char -> Nat -> Prop
  | bal, [], finish => finish = bal
  | bal, c :: xs, finish =>
      if c = '(' then
        Run (bal + 1) xs finish
      else if c = ')' then
        match bal with
        | 0 => False
        | bal + 1 => Run bal xs finish
      else
        False

theorem run_append {xs ys : List Char} {start mid finish : Nat} :
    Run start xs mid -> Run mid ys finish -> Run start (xs ++ ys) finish := by
  induction xs generalizing start with
  | nil =>
      intro hxs hys
      simp [Run] at hxs
      subst mid
      exact hys
  | cons c xs ih =>
      intro hxs hys
      by_cases hcopen : c = '('
      · subst c
        simp [Run] at hxs ⊢
        exact ih hxs hys
      · by_cases hcclose : c = ')'
        · subst c
          cases start with
          | zero =>
              simp [Run] at hxs
          | succ start =>
              simp [Run] at hxs ⊢
              exact ih hxs hys
        · simp [Run, hcopen, hcclose] at hxs

theorem run_to_validFrom {xs : List Char} {start : Nat} :
    Run start xs 0 -> ValidFrom start xs := by
  induction xs generalizing start with
  | nil =>
      intro h
      simp [Run] at h
      simp [ValidFrom, h.symm]
  | cons c xs ih =>
      intro h
      by_cases hcopen : c = '('
      · subst c
        simp [Run] at h
        simpa [ValidFrom] using ih h
      · by_cases hcclose : c = ')'
        · subst c
          cases start with
          | zero =>
              simp [Run] at h
          | succ start =>
              simp [Run] at h
              simpa [ValidFrom] using ih h
        · simp [Run, hcopen, hcclose] at h

theorem correct_ne_nil {xs : List Char} :
    CorrectParenString xs -> xs ≠ [] := by
  intro h
  induction h with
  | unit =>
      simp
  | wrap h ih =>
      simp
  | concat hS hT ihS ihT =>
      intro happ
      exact ihS (List.append_eq_nil_iff.mp happ).1

theorem correct_run_same {xs : List Char} :
    CorrectParenString xs -> ∀ bal, Run bal xs bal := by
  intro h
  induction h with
  | unit =>
      intro bal
      cases bal <;> simp [Run]
  | wrap h ih =>
      intro bal
      simp [Run]
      exact run_append (ih (bal + 1)) (by cases bal <;> simp [Run])
  | concat hS hT ihS ihT =>
      intro bal
      exact run_append (ihS bal) (ihT bal)

theorem correct_validFrom_zero {xs : List Char} :
    CorrectParenString xs -> xs ≠ [] ∧ ValidFrom 0 xs := by
  intro h
  exact ⟨correct_ne_nil h, run_to_validFrom (correct_run_same h 0)⟩

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

def LexLe : List Char -> List Char -> Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => (x = '(' ∧ y = ')') ∨ (x = y ∧ LexLe xs ys)

def LexSorted (answer : List (List Char)) : Prop :=
  answer.Pairwise LexLe

theorem lex_prefix {c : Char} {xs ys : List Char} :
    LexLe xs ys -> LexLe (c :: xs) (c :: ys) := by
  intro h
  simp [LexLe, h]

theorem lex_open_close {xs ys : List Char} : LexLe ('(' :: xs) (')' :: ys) := by
  simp [LexLe]

theorem gen_lex_sorted (rem bal : Nat) : LexSorted (gen rem bal) := by
  induction rem generalizing bal with
  | zero =>
      by_cases hbal : bal = 0 <;> simp [gen, hbal, LexSorted]
  | succ rem ih =>
      by_cases hbal : bal = 0
      · have hleft : LexSorted ((gen rem (bal + 1)).map (fun xs => '(' :: xs)) :=
          List.Pairwise.map _ (fun _ _ h => lex_prefix h) (ih (bal + 1))
        simpa [gen, hbal, LexSorted] using hleft
      · have hleft : LexSorted ((gen rem (bal + 1)).map (fun xs => '(' :: xs)) :=
          List.Pairwise.map _ (fun _ _ h => lex_prefix h) (ih (bal + 1))
        have hright : LexSorted ((gen rem (bal - 1)).map (fun xs => ')' :: xs)) :=
          List.Pairwise.map _ (fun _ _ h => lex_prefix h) (ih (bal - 1))
        have hcross :
            ∀ a, a ∈ (gen rem (bal + 1)).map (fun xs => '(' :: xs) ->
            ∀ b, b ∈ (gen rem (bal - 1)).map (fun xs => ')' :: xs) ->
              LexLe a b := by
          intro a ha b hb
          rcases List.mem_map.mp ha with ⟨xs, _, rfl⟩
          rcases List.mem_map.mp hb with ⟨ys, _, rfl⟩
          exact lex_open_close
        have happ :
            LexSorted
              (((gen rem (bal + 1)).map (fun xs => '(' :: xs)) ++
                ((gen rem (bal - 1)).map (fun xs => ')' :: xs))) :=
          List.pairwise_append.mpr ⟨hleft, hright, hcross⟩
        simpa [gen, hbal, LexSorted] using happ

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
      apply validFrom_zero_correct
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
    exact False.elim ((correct_validFrom_zero hcorrect).1 this)
  · simp [solve, hN]
    exact gen_complete hlen (correct_validFrom_zero hcorrect).2

def SolutionIsValid (N : Nat) (answer : List (List Char)) : Prop :=
  (∀ xs, xs ∈ answer -> xs.length = N ∧ IsCorrectParenString xs) ∧
    (∀ xs, xs.length = N -> IsCorrectParenString xs -> xs ∈ answer) ∧
      LexSorted answer

theorem solution_is_valid (N : Nat) : SolutionIsValid N (solve N) := by
  constructor
  · intro xs hmem
    exact solve_sound hmem
  · constructor
    · intro xs hlen hcorrect
      exact solve_complete hlen hcorrect
    · unfold solve
      split
      · simp [LexSorted]
      · exact gen_lex_sorted N 0

def readNat (s : String) : Nat :=
  match s.split (fun c => c = ' ' || c = '\n' || c = '\t' || c = '\r') |>.filter (· ≠ "") with
  | token :: _ => token.toNat!
  | [] => 0

def main : IO Unit := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  printSolution (solve (readNat input))
