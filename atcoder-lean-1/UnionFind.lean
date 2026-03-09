-- import Mathlib.Logic.Relation

structure UnionFindVector (n : Nat) where
  internal_mk ::
  parent : Vector (Fin n) n
  size : Vector Nat n
  inv_parent_size : ∀ i : Fin n, i = parent[i] ∨ size[i] < size[parent[i]]
  max_size : Nat
  inv_max_size : ∀ i : Fin n, size[i] <= max_size

def UnionFindVector.make (n : Nat) : UnionFindVector n :=
  {
    parent := Vector.ofFn (fun i => i)
    size := Vector.ofFn (fun _ => 1)
    inv_parent_size := by simp
    max_size := 1
    inv_max_size := by simp
  }

/--
  iの同値類を表す数を得る関数。

  TODO: 不変条件を適切に設定して、この関数の停止性を示す。
  おそらく (n+1-rank) あたりが再帰で減少すると示しやすいのではなかろうか。
  後のために、「返ってきたものは代表元だ」という証明も一緒に返さないとダメかもしれない。
  いや、普通に定義を使ってtheoremを作ればいいだけか。
-/
def UnionFindVector.find (uf : UnionFindVector n) (i : Fin n) :=
  let pi := uf.parent[i]
  if pi = i then
    i
  else
    uf.find pi
termination_by uf.max_size - uf.size[i]
decreasing_by
  have h_inv_parent_size := uf.inv_parent_size i
  cases h_inv_parent_size
  case inl => grind
  case inr =>
    have h_inv_max_size_i := uf.inv_max_size i
    have h_inv_max_size_pi := uf.inv_max_size pi
    grind

structure UnionFindVectorRepresentative (n : Nat) (uf : UnionFindVector n) where
  i : Fin n
  i_is_representative : uf.parent[i] = i

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
        have h : (uf.parent.set (↑i_child) i_parent)[(↑i : Nat)] = uf.parent[↑i] := by
          apply Vector.getElem_set_ne
          case h => grind only [Fin.eq_of_val_eq]
        simp [h]
        sorry
    max_size := uf.max_size.max (sp + sc)
    inv_max_size := sorry
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
  - sizeを追加してunion-by-sizeを実装
  - 「グループリーダーにわたるsizeの総和がn」を示し、そこからfindの停止性を示す
  - (後で。優先度低)sizeがちゃんとサイズになっていることを示す。
    - 集合のサイズの定義自体、何を使えばいいか……という感じなので、後回しが良さそう
-/
