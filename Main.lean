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

def solve (n l k : Nat) (a : Array Nat) {nc : n >= 1} {alen : a.size = n} : Nat :=
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
  binary_search isAchievable 1 l

def main : IO Unit := do
  let stdin ← IO.getStdin
  let instr ← stdin.readToEnd
  let intokens := (instr.split (·.isWhitespace)).toArray
  let n := intokens[0]!.trim.toNat!
  if nc : n < 1 then unreachable! else
  let l := intokens[1]!.trim.toNat!
  let k := intokens[2]!.trim.toNat!
  let a := Array.ofFn (n := n) fun i =>
    intokens[i.val + 3]!.trim.toNat!
  -- TODO: この仮定は人工的に与えなくてすむはず
  if alen : a.size != n then unreachable! else
  let solution := solve n l k a (nc := by grind) (alen := by grind)
  IO.println s!"{solution}"
