/-
  using binary search to find the point where
  the predicate p changes from true to false.
-/
def binary_search (pred : Nat → Bool) (left : Nat) (right : Nat) : Nat :=
  if right - left <= 1 then
    left
  else
    let mid := (left + right) / 2
    if pred mid then
      binary_search pred mid right
    else
      binary_search pred left mid

abbrev maximum (n : Nat) (pred : Nat → Prop) : Prop :=
  pred n ∧ ∀ m, (m > n) → ¬ pred m

abbrev monotone (pred : Nat → Prop) : Prop :=
  ∀ m n, (m <= n) → pred n → pred m

theorem monotone_maximum_from_one_step
  (pred : Nat → Prop)
  (h_monotone : monotone pred)
  (n : Nat)
  (h_n : pred n)
  (h_n1 : ¬ pred (n + 1))
  : maximum n pred := by grind

theorem binary_search_is_valid
  (pred : Nat → Bool) (left : Nat) (right : Nat)
  (h_monotone : monotone (pred · = true))
  (h_left : pred left = true)
  (h_right : pred right = false)
  : maximum (binary_search pred left right) (pred · = true) :=
by
  fun_induction binary_search with grind

abbrev upper (pred : Nat → Prop) (n : Nat) : Prop :=
  ∃ m, m >= n ∧ pred m

theorem upper_is_monotone
  (pred : Nat → Prop)
  : monotone (upper pred) := by grind

theorem upper_maximum_is_maximum
  (n : Nat)
  (pred : Nat → Prop)
  (h_upper_max : maximum n (upper pred))
  : maximum n pred :=
by
  constructor
  case left =>
    sorry
  case right =>
    grind
