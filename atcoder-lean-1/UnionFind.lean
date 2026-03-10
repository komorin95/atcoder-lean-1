-- import Mathlib.Logic.Relation

structure UnionFindVector (n : Nat) where
  internal_mk ::
  parent : Vector (Fin n) n
  size : Vector Nat n
  inv_size : ∀ i : Fin n, 1 <= size[i]
  inv_parent_size : ∀ i : Fin n, i = parent[i] ∨ size[i] < size[parent[i]]

def UnionFindVector.make (n : Nat) : UnionFindVector n :=
  {
    parent := Vector.ofFn (fun i => i)
    size := Vector.ofFn (fun _ => 1)
    inv_size := by simp
    inv_parent_size := by simp
  }

/--
  iの同値類を表す数を得る関数。
-/
def UnionFindVector.find (uf : UnionFindVector n) (i : Fin n) :=
  let pi := uf.parent[i]
  if pi = i then
    i
  else
    uf.find pi
termination_by uf.size.toList.max?.getD 0 - uf.size[i]
decreasing_by
  have h_inv_parent_size := uf.inv_parent_size i
  have h_max : ∀ ii : Fin n, uf.size[ii] <= uf.size.toList.max?.getD 0 := by
    intro
    apply List.le_max?_getD_of_mem
    simp
  grind

theorem parent_find_eq_find (uf : UnionFindVector n) (i : Fin n)
  : uf.parent[uf.find i] = uf.find i :=
by
   fun_induction UnionFindVector.find with grind only

@[simp]
theorem parent_find_eq_find_simpNF (uf : UnionFindVector n) (i : Fin n)
  : uf.parent[(↑(uf.find i) : Nat)] = uf.find i :=
by
  have := parent_find_eq_find uf i
  simp at this
  assumption

def UnionFindVector.internal_naive_union
  (uf : UnionFindVector n) (i_parent i_child : Fin n)
  (cond_ip : uf.parent[i_parent] = i_parent)
  (cond_ip_ic : ¬ i_parent = i_child) : UnionFindVector n :=
  let sp := uf.size[i_parent]
  let sc := uf.size[i_child]
  {
    parent := uf.parent.set i_child i_parent
    size := uf.size.set i_parent (sp + sc)
    inv_size := by
      have := uf.inv_size
      simp_all (config := {zetaDelta := true}) [Vector.getElem_set]
      grind only [Fin.eq_of_val_eq]
    inv_parent_size := by
      intro i
      by_cases h_i_ic : i_child = i
      case pos =>
        simp [*]
        right
        have : (↑i_parent : Nat) ≠ ↑i := by grind only [Fin.eq_of_val_eq]
        simp [*]
        have h_sp := uf.inv_size i_parent
        have h_sc : uf.size[(↑i : Nat)] = sc := by
          simp (config := {zetaDelta := true})
          grind only
        grind only
      case neg =>
        have h_i_ic : (↑i_child : Nat) ≠ ↑i := by grind only [Fin.eq_of_val_eq]
        simp [*]
        by_cases h_ip_i : i_parent = i
        case pos =>
          left
          simp_all
        case neg =>
          have h_ip_i : (↑i_parent : Nat) ≠ ↑i := by grind only [Fin.eq_of_val_eq]
          simp [*]
          by_cases h_ip_pari : i_parent = uf.parent[i]
          case pos =>
            unfold sp
            simp_all
            cases uf.inv_parent_size i
            case inl => grind only
            case inr =>
              simp_all
              grind only
          case neg =>
            have h_inv_i := uf.inv_parent_size i
            simp_all [Vector.getElem_set]
            grind only [Fin.eq_of_val_eq]
  }

def UnionFindVector.union (uf : UnionFindVector n) (i j : Fin n) : UnionFindVector n :=
  let ci := uf.find i
  let cj := uf.find j
  if cond_i : ci = cj then
    uf
  else
    let si := uf.size[ci]
    let sj := uf.size[cj]
    if si > sj then
      uf.internal_naive_union ci cj (by simp (config := {zetaDelta := true})) (by grind only)
    else
      uf.internal_naive_union cj ci (by simp (config := {zetaDelta := true})) (by grind only)

/-
  TODO:
  - EqvGenを使ってUnionFindの「意味」を定式化
  - (後で。優先度低)sizeがちゃんとサイズになっていることを示す。
    - 集合のサイズの定義自体、何を使えばいいか……という感じなので、後回しが良さそう
-/
