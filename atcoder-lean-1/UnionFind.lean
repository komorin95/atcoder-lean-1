-- import Mathlib.Logic.Relation

def Vector.max [Max α] (xs : Vector α n) (h : n > 0 := by simp_all) : α :=
  let max_o := xs.toList.max?
  have h_is_some : max_o.isSome := by
    have : ∃ a : α, a ∈ xs.toList := by
      apply List.length_pos_iff_exists_mem.mp
      simp_all
    grind [List.isSome_max?_of_mem]
  max_o.get h_is_some

theorem Vector.le_max_of_getElem_fin {xs : Vector Nat n} {i : Fin n} (hn : n > 0)
  : xs[i] <= xs.max :=
by
  unfold Vector.max
  simp
  apply List.le_max?_get_of_mem
  simp

structure UnionFindVector (n : Nat) where
  internal_mk ::
  parent : Vector (Fin n) n
  size : Vector Nat n
  inv_parent_size : ∀ i : Fin n, i = parent[i] ∨ size[i] < size[parent[i]]

def UnionFindVector.make (n : Nat) : UnionFindVector n :=
  {
    parent := Vector.ofFn (fun i => i)
    size := Vector.ofFn (fun _ => 1)
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
termination_by (if h : n = 0 then 0 else uf.size.max (by grind only)) - uf.size[i]
decreasing_by
  have hn_nonzero : n ≠ 0 := by
    have hi := i.isLt
    grind only
  have hn_gtzero : n > 0 := by grind only
  have h_pi : uf.parent[i] = pi := by grind only
  simp [*]
  have h_inv_parent_size := uf.inv_parent_size i
  cases h_inv_parent_size
  case inl => grind
  case inr =>
    have : uf.size[i] <= uf.size.max := by grind only [Vector.le_max_of_getElem_fin]
    have : uf.size[pi] <= uf.size.max := by grind only [Vector.le_max_of_getElem_fin]
    simp_all
    grind

theorem parent_find_eq_find (uf : UnionFindVector n) (i : Fin n)
  : uf.parent[uf.find i] = uf.find i :=
by
   fun_induction UnionFindVector.find with grind only

theorem Vector.getElem_set_ne_fin {i j : Fin n} {xs : Vector α n} {x : α}
  (h : i ≠ j) : (xs.set ↑i x)[j] = xs[j] :=
by
  apply Vector.getElem_set_ne
  grind only [Fin.eq_of_val_eq]

def UnionFindVector.internal_naive_union
  (uf : UnionFindVector n) (i_parent i_child : Fin n)
  (cond_i : ¬ i_parent = i_child) : UnionFindVector n :=
  let sp := uf.size[i_parent]
  let sc := uf.size[i_child]
  {
    parent := uf.parent.set i_child i_parent
    size := uf.size.set i_parent (sp + sc)
    inv_parent_size := by
      intro i
      by_cases h_i : i = i_child
      case pos =>
        sorry
      case neg =>
        have h : i_child ≠ i := by grind only
        -- hを入れないとsimpできない。なんでだ
        simp [Vector.getElem_set_ne_fin h]
        sorry
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
      uf.internal_naive_union ci cj (by grind only)
    else
      uf.internal_naive_union cj ci (by grind only)

/-
  TODO:
  - EqvGenを使ってUnionFindの「意味」を定式化
  - (後で。優先度低)sizeがちゃんとサイズになっていることを示す。
    - 集合のサイズの定義自体、何を使えばいいか……という感じなので、後回しが良さそう
-/
