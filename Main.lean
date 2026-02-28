import Mathlib.Data.List.Chain

-- BinarySearch.lean start

def binarySearch (pred : Nat → Bool) (left : Nat) (right : Nat) : Nat :=
  if right - left <= 1 then
    left
  else
    let mid := (left + right) / 2
    if pred mid then
      binarySearch pred mid right
    else
      binarySearch pred left mid

abbrev maximum (n : Nat) (pred : Nat → Prop) : Prop :=
  pred n ∧ ∀ m, (m > n) → ¬ pred m

abbrev monotone (pred : Nat → Prop) : Prop :=
  ∀ m n, (m <= n) → pred n → pred m

theorem binarySearchIsValid
  (pred : Nat → Bool) (left : Nat) (right : Nat)
  (h_monotone : monotone (pred · = true))
  (h_left : pred left = true)
  (h_right : pred right = false)
  : maximum (binarySearch pred left right) (pred · = true) :=
by
  fun_induction binarySearch with grind

abbrev upper (pred : Nat → Prop) (n : Nat) : Prop :=
  ∃ m, m >= n ∧ pred m

theorem upperMaximumIsMaximum
  (n : Nat)
  (pred : Nat → Prop)
  (h_upper_max : maximum n (upper pred))
  : maximum n pred :=
by
  obtain ⟨m, h_m⟩ := h_upper_max.left
  have : ¬ m > n := by grind
  grind

theorem binarySearchForNonmonotone
  (pred0 : Nat → Prop)
  (pred : Nat → Bool)
  (h_pred : ∀ n, pred n = true ↔ upper pred0 n)
  (left : Nat) (right : Nat)
  (h_left : pred left = true)
  (h_right : pred right = false)
  : maximum (binarySearch pred left right) pred0 :=
by
  apply upperMaximumIsMaximum
  have pred_calc_upper : (upper pred0) = (pred · = true) := by grind
  rw [pred_calc_upper]
  apply binarySearchIsValid
  grind
  grind
  grind

-- BinarySearch.lean end

def solve0 (n l k : Nat) (a : Array Nat) {nc : n >= 1} {alen : a.size = n} : Nat :=
  let zero_to_n := List.finRange n
  let rec isAchievable (score : Nat) : Bool := Id.run do
    let mut curr_len := 0
    let mut curr_k := k
    for ifin in zero_to_n do
      let i := ifin.val -- こうしないと配列アクセスの!が消せない
      let this_piece := if i == 0 then a[0] else a[i] - a[i-1]
      curr_len := curr_len + this_piece
      if curr_k > 0 && curr_len >= score then
        curr_k := curr_k - 1
        curr_len := 0
    if curr_k > 0 then return false
    let last_piece := l - a[n-1]
    curr_len := curr_len + last_piece
    return curr_len >= score
  binarySearch isAchievable 1 l

structure ProblemInput where
  n : Nat
  cond_n : n <= 100_000
  k : Nat
  cond_k : 1 <= k
  cond_kn : k <= n
  a : List Nat
  cond_an : a.length = n
  cond_a : List.Chain (α := Nat) (· < ·) 0 a
  l : Nat
  cond_l : a.getLast (by grind) < l

def partialScore (a0 : Nat) (a : List Nat) (l : Nat) :=
  match a with
  | [] => l - a0
  | a1 :: as => min (a1 - a0) (partialScore a1 as l)

def score (input : ProblemInput) (b : List Nat) :=
  partialScore 0 b input.l

abbrev scoreAchievableBy (input : ProblemInput) (b : List Nat) (s : Nat) : Prop :=
  List.Sublist b input.a
  ∧ b.length = input.k
  ∧ score input b = s

abbrev scoreAchievable (input : ProblemInput) (s : Nat) : Prop :=
  ∃ b, scoreAchievableBy input b s

def scoreOfPartitionRec (a : List Nat) : Nat :=
  match a with
  | [x, y] => y - x
  | x :: (y :: a) => min (y - x) (scoreOfPartitionRec (y :: a))
  | _ => unreachable!

def isAchievable (input : ProblemInput) (score : Nat) : Bool := false

def solve (input : ProblemInput) : Nat := 0

theorem solutionIsValid (input : ProblemInput)
  : maximum (solve input) (scoreAchievable input) := sorry

def main : IO Unit := do
  let stdin ← IO.getStdin
  let instr ← stdin.readToEnd
  let intokens := (instr.split (·.isWhitespace)).toArray
  let n := intokens[0]!.trim.toNat!
  if cond_n : n > 100_000 then unreachable! else
  let l := intokens[1]!.trim.toNat!
  let k := intokens[2]!.trim.toNat!
  if cond_k : k < 1 then unreachable! else
  if cond_kn : k > n then unreachable! else
  let a := List.ofFn (n := n) fun i =>
    intokens[i.val + 3]!.trim.toNat!
  -- TODO: この仮定は人工的に与えなくてすむはず
  if cond_an : a.length != n then unreachable! else
  if cond_a : ¬ List.Chain (α := Nat) (· < ·) 0 a then unreachable! else
  if cond_l : a.getLast (by grind) >= l then unreachable! else
  let input : ProblemInput := {
    n := n
    cond_n := by grind
    k := k
    cond_k := by grind
    cond_kn := by grind
    a := a
    cond_an := by grind
    cond_a := by grind
    l := l
    cond_l := by grind
  }
  let solution := solve input
  IO.println s!"{solution}"
