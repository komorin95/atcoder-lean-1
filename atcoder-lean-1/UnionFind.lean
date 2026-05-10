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
def UnionFindVector.find (uf : UnionFindVector n) (i : Fin n) : Fin n :=
  let pi := uf.parent[i]
  if pi = i then
    i
  else
    uf.find pi
termination_by uf.size.toList.max?.getD 0 - uf.size[i]
decreasing_by
  have := uf.inv_parent_size
  have h_max : ∀ ii : Fin n, uf.size[ii] <= uf.size.toList.max?.getD 0 := by
    intro
    apply List.le_max?_getD_of_mem
    simp
  grind

theorem find_make_eq_id (i : Fin n)
  : (UnionFindVector.make n).find i = i :=
by
  simp [UnionFindVector.make, UnionFindVector.find]

theorem parent_find_eq_find (uf : UnionFindVector n) (i : Fin n)
  : uf.parent[uf.find i] = uf.find i :=
by
  fun_induction UnionFindVector.find with grind only

@[simp]
theorem parent_find_eq_find_simpNF (uf : UnionFindVector n) (i : Fin n)
  : uf.parent[(uf.find i).val] = uf.find i :=
by
  have := parent_find_eq_find uf i
  simp at this
  assumption

structure UnionFindPathCompData (n : Nat) (i : Fin n) (size : Vector Nat n) where
  uf : UnionFindVector n
  ri : Fin n
  h_pathcomp : uf.parent[i] = ri
  h_size : uf.size = size

def UnionFindVector.findHelper (uf : UnionFindVector n) (i : Fin n)
  : UnionFindPathCompData n i uf.size :=
  let pi := uf.parent[i]
  if h_if : pi = i then
    {
      uf := uf
      ri := i
      h_pathcomp := by simp_all [pi]
      h_size := by simp
    }
  else
    let ⟨uf1, ri, h_pathcomp1, h_size⟩ := uf.findHelper pi
    let uf_new := {
      parent := uf1.parent.set i ri
      size := uf1.size
      inv_size := uf1.inv_size
      inv_parent_size := by
        have := uf1.inv_size
        have := uf1.inv_parent_size
        have := h_pathcomp1
        have : uf1.size[pi] <= uf1.size[ri] := by grind
        have : uf1.size[i] < uf1.size[ri] := by
          have := uf.inv_parent_size i
          simp [pi] at *
          grind
        simp_all +zetaDelta [Vector.getElem_set]
        grind only [cases Or]
    }
    {
      uf := uf_new
      ri := ri
      h_pathcomp := by simp [uf_new]
      h_size := by simp [uf_new, h_size]
    }
termination_by uf.size.toList.max?.getD 0 - uf.size[i]
decreasing_by
  have := uf.inv_parent_size
  have h_max : ∀ ii : Fin n, uf.size[ii] <= uf.size.toList.max?.getD 0 := by
    intro
    apply List.le_max?_getD_of_mem
    simp
  grind

def UnionFindVector.findWithPC (uf : UnionFindVector n) (i : Fin n) : UnionFindVector n × Fin n :=
  let ⟨uf1, root, _, _⟩ := uf.findHelper i
  ⟨uf1, root⟩

theorem snd_findWithPC_eq_find (uf : UnionFindVector n) (i : Fin n)
  : (uf.findWithPC i).snd = uf.find i :=
by
  unfold UnionFindVector.findWithPC
  simp
  fun_induction UnionFindVector.findHelper
  case case1 pi h =>
    simp_all +zetaDelta [UnionFindVector.find]
  case case2 pi h _ _ x _ ih =>
    simp [pi] at h
    simp [x] at ih
    simp
    unfold UnionFindVector.find
    simp [h]
    assumption

/--
  simpで上手に添え字を扱うための補題。
  複雑になる方向に見えるが、後の簡約を考えるとこの向きが正解な気がする。
-/
@[simp]
theorem Fin.eq_iff_eq_of_val {i j : Fin n}
  : i = j ↔ i.val = j.val :=
by
  constructor
  apply Fin.val_eq_of_eq
  apply Fin.eq_of_val_eq

def UnionFindVector.internal_naive_union
  (uf : UnionFindVector n) (i_parent i_child : Fin n)
  (cond_ip : uf.parent[i_parent] = i_parent)
  : UnionFindVector n :=
  let sp := uf.size[i_parent]
  let sc := uf.size[i_child]
  {
    parent := uf.parent.set i_child i_parent
    size := uf.size.set i_parent (sp + sc)
    inv_size := by
      have := uf.inv_size
      simp_all +zetaDelta [Vector.getElem_set]
      grind only
    inv_parent_size := by
      have := uf.inv_size
      have := uf.inv_parent_size
      simp_all +zetaDelta [Vector.getElem_set]
      grind only [cases Or]
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
      uf.internal_naive_union ci cj (by simp [ci])
    else
      uf.internal_naive_union cj ci (by simp [cj])

/-
  TODO:
  - EqvGenを使ってUnionFindの「意味」を定式化
  - (後で。優先度低)sizeがちゃんとサイズになっていることを示す。
    - 集合のサイズの定義自体、何を使えばいいか……という感じなので、後回しが良さそう
-/
