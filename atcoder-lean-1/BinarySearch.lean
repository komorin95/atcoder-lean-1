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

theorem upper_maximum_is_maximum
  (n : Nat)
  (pred : Nat → Prop)
  (h_upper_max : maximum n (upper pred))
  : maximum n pred :=
by
  obtain ⟨m, h_m⟩ := h_upper_max.left
  have : ¬ m > n := by grind
  grind

theorem binary_search_for_nonmonotone
  (pred0 : Nat → Prop)
  (pred : Nat → Bool)
  (h_pred : ∀ n, pred n = true ↔ upper pred0 n)
  (left : Nat) (right : Nat)
  (h_left : pred left = true)
  (h_right : pred right = false)
  : maximum (binary_search pred left right) pred0 :=
by
  apply upper_maximum_is_maximum
  have pred_calc_upper : (upper pred0) = (pred · = true) := by grind
  rw [pred_calc_upper]
  apply binary_search_is_valid
  grind
  grind
  grind
