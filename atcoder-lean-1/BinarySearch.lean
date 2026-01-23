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

theorem binary_search_is_valid
  (pred : Nat → Bool) (left : Nat) (right : Nat)
  (h_monotone : ∀ m n, (m <= n) → pred n = true → pred m = true)
  (h_left : pred left = true)
  (h_right : pred right = false)
  : (pred (binary_search pred left right) = true)
  ∧ (pred ((binary_search pred left right) + 1) = false) :=
by
  fun_induction binary_search with grind
