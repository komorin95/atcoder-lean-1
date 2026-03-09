-- import Mathlib.Logic.Relation

structure UnionFindVector (n : Nat) where
  internal_mk ::
  parent : Vector (Fin n) n
  size : Vector Nat n

def UnionFindVector.make (n : Nat) : UnionFindVector n :=
  {
    parent := Vector.ofFn (fun i => i)
    size := Vector.ofFn (fun _ => 1)
  }

/--
  iの同値類を表す数を得る関数。

  TODO: 不変条件を適切に設定して、この関数の停止性を示す。
  おそらく (n+1-rank) あたりが再帰で減少すると示しやすいのではなかろうか。
-/
partial def UnionFindVector.find (uf : UnionFindVector n) (i : Fin n) :=
  let pi := uf.parent[i]
  if pi = i then
    i
  else
    uf.find pi

def UnionFindVector.union (uf : UnionFindVector n) (i j : Fin n) : UnionFindVector n :=
  let ci := uf.find i
  let cj := uf.find j
  if ci = cj then
    uf
  else
    let si := uf.size[i]
    let sj := uf.size[j]
    if si > sj then
      {
        parent := uf.parent.set j i
        size := uf.size.set i (si + sj)
      }
    else
      {
        parent := uf.parent.set i j
        size := uf.size.set j (si + sj)
      }

/-
  TODO:
  - EqvGenを使ってUnionFindの「意味」を定式化
  - sizeを追加してunion-by-sizeを実装
  - 「グループリーダーにわたるsizeの総和がn」を示し、そこからfindの停止性を示す
  - (後で。優先度低)sizeがちゃんとサイズになっていることを示す。
    - 集合のサイズの定義自体、何を使えばいいか……という感じなので、後回しが良さそう
-/
