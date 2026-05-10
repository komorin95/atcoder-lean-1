/-
  競プロ典型90問1日目「Yokan Party」の検証済み解答
  解答プログラムのみのバージョン
-/

import Mathlib.Data.List.Chain

structure ProblemInput where
  n : Nat
  k : Nat
  a : List Nat
  l : Nat

/--
  二分探索を行い、predがtrueからfalseに変わる点をleftとrightの間で探す関数。
-/
def binarySearch (pred : Nat → Bool) (left : Nat) (right : Nat) : Nat :=
  if right - left <= 1 then
    left
  else
    let mid := (left + right) / 2
    if pred mid then
      binarySearch pred mid right
    else
      binarySearch pred left mid

/--
  「a0からlの座標を占めるようかんを、aから選んだlen箇所で切ることで、
  score以上のスコアが実現できるか」を貪欲法で判定する関数。
-/
def betterScoreAchievableRec (a0 : Nat) (a : List Nat) (l len score : Nat) : Bool :=
  if len == 0 then
    l - a0 >= score
  else
    match a with
    | [] => false
    | a1 :: as =>
      if a1 - a0 >= score then
        betterScoreAchievableRec a1 as l (len - 1) score
      else
        betterScoreAchievableRec a0 as l len score

/--
  「inputのもとで、score以上のスコアが実現できるか？」を貪欲法で判定する関数。
-/
def betterScoreAchievable (input : ProblemInput) (score : Nat) : Bool :=
  betterScoreAchievableRec 0 input.a input.l input.k score

/--
  貪欲法によるスコア閾値達成可能性の判定と二分探索を組み合わせ、最大スコアを求める関数。
-/
def solve (input : ProblemInput) : Nat :=
  binarySearch (betterScoreAchievable input) 0 (input.l + 1)

/--
  エントリーポイント
-/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let instr ← stdin.readToEnd
  let intokens := (instr.split (·.isWhitespace)).toArray
  let n := intokens[0]!.trim.toNat!
  let l := intokens[1]!.trim.toNat!
  let k := intokens[2]!.trim.toNat!
  let a := List.ofFn (n := n) fun i =>
    intokens[i.val + 3]!.trim.toNat!
  let input : ProblemInput := {
    n := n
    k := k
    a := a
    l := l
  }
  let solution := solve input
  IO.println s!"{solution}"
