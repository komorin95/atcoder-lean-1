/-
  競プロ典型90問1日目「Yokan Party」の検証済み解答
  問題設定・解答プログラム・正当性証明 の順に示す
-/

import Mathlib.Data.List.Chain

/-
  ==================問題設定==================
-/

/--
  問題の入力と、それらについての条件。
-/
structure ProblemInput where
  n : Nat
  l : Nat
  k : Nat
  a : List Nat
  cond_n : n <= 100_000
  cond_k : 1 <= k
  cond_kn : k <= n
  cond_an : a.length = n
  cond_l : l <= 1_000_000_000
  cond_al : List.Chain (α := Nat) (· < ·) 0 (a ++ [l])

/--
  a0からlの座標を占めるようかんの切れ端を、aの各座標で切ったときの、ようかんの最小サイズを計算する関数。

  実行時には呼び出されないが、条件の定義に必要。
-/
@[grind]
def scoreRec (a0 : Nat) (a : List Nat) (l : Nat) :=
  match a with
  | [] => l - a0
  | a1 :: as => min (a1 - a0) (scoreRec a1 as l)

/--
  「a0からlの座標を占めるようかんを、aから選んだlen箇所の位置bで切ることで、
  スコアscoreが実現する」という条件。
-/
abbrev scoreAchievablePartialBy (a0 : Nat) (a : List Nat) (l len score : Nat) (b : List Nat) : Prop :=
  List.Sublist b a
  ∧ b.length = len
  ∧ scoreRec a0 b l = score

/--
  「inputのもとで、bの各座標で切ればスコアsが実現する」という条件。
-/
abbrev scoreAchievableBy (input : ProblemInput) (b : List Nat) (s : Nat) : Prop :=
  scoreAchievablePartialBy 0 input.a input.l input.k s b

/--
  「inputのもとでスコアsが実現可能である」という条件。
-/
abbrev scoreAchievable (input : ProblemInput) (s : Nat) : Prop :=
  ∃ b, scoreAchievableBy input b s

/--
  「nはpredを満たす最大の自然数である」という条件。
-/
abbrev maximum (n : Nat) (pred : Nat → Prop) : Prop :=
  pred n ∧ ∀ m, (m > n) → ¬ pred m

/--
  「全ての入力に対して、solutionが返す解答は正当である」という条件。

  これを満たす関数を作り、証明を与えることが目標。
-/
abbrev abbrevSolutionIsValid (solution : ProblemInput → Nat) :=
  ∀ input : ProblemInput, maximum (solution input) (scoreAchievable input)

/-
  ==================解答プログラム==================
-/

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

  この関数の正当性が今回の目標になる。
-/
def solve (input : ProblemInput) : Nat :=
  binarySearch (betterScoreAchievable input) 0 (input.l + 1)

section

open String (Iterator)

abbrev InputReader := EStateM Unit Iterator

partial def skipWhiteSpacesHelper (iter : Iterator) : Iterator :=
  if iter.atEnd || !iter.curr.isWhitespace then
    iter
  else
    skipWhiteSpacesHelper iter.next

def skipWhiteSpaces : InputReader Unit :=
  EStateM.modifyGet fun iter => ⟨(), skipWhiteSpacesHelper iter⟩

partial def readNatHelper (num : Nat) (iter : Iterator) : Nat × Iterator :=
  if iter.atEnd || !iter.curr.isDigit then
    (num, iter)
  else
    let digit := iter.curr.toNat - 48
    readNatHelper (num * 10 + digit) iter.next

def readNat : InputReader Nat := do
  skipWhiteSpaces
  let iter ← EStateM.get
  if iter.atEnd || !iter.curr.isDigit then
    EStateM.throw ()
  let num ← EStateM.modifyGet (readNatHelper 0)
  return num

def checkCondition {p : Prop} [Decidable p] : InputReader (PLift p) := do
  if condition : p then
    return .up condition
  else
    EStateM.throw ()

def readFin (n : Nat) : InputReader (Fin n) := do
  return ⟨(← readNat), (← checkCondition).down⟩

end

/--
  入力パーサー。

  EStateMモナドを使って、文字列上のIteratorの扱いを省略しつつ、
  条件チェックに対するエラー処理を行っている。
-/
def readProblemInput : InputReader ProblemInput := do
  let n ← readNat
  return {
    n := n
    l := (← readNat)
    k := (← readNat)
    a := (← List.ofFnM (n := n) fun _ => readNat)

    cond_n := (← checkCondition).down
    cond_k := (← checkCondition).down
    cond_kn := (← checkCondition).down
    cond_al := (← checkCondition).down
    cond_l := (← checkCondition).down
    cond_an := (← checkCondition).down -- TODO: これは証明できるはず
  }

/--
  エントリーポイント。
-/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let instr ← stdin.readToEnd
  match readProblemInput.run instr.iter with
  | .error _ _ => unreachable!
  | .ok input _ => do
    let solution := solve input
    IO.println s!"{solution}"

/-
  ==================正当性証明==================
-/

/--
  「predは"単調減少"である」という条件。
-/
abbrev monotone (pred : Nat → Prop) : Prop :=
  ∀ m n, (m <= n) → pred n → pred m

/--
  二分探索が正当である、という定理。
-/
theorem binarySearchIsValid
  (pred : Nat → Bool) (left : Nat) (right : Nat)
  (h_monotone : monotone (pred · = true))
  (h_left : pred left = true)
  (h_right : pred right = false)
  : maximum (binarySearch pred left right) (pred · = true) :=
by
  fun_induction binarySearch with grind

/--
  「n以上の数でpredが成り立つようなものが存在する」という条件。
-/
abbrev upper (pred : Nat → Prop) (n : Nat) : Prop :=
  ∃ m, m >= n ∧ pred m

/--
  「(upper pred)が成り立つ最大値とpredが成り立つ最大値は等しい」という定理。
-/
theorem upperMaximumIsMaximum
  (n : Nat)
  (pred : Nat → Prop)
  (h_upper_max : maximum n (upper pred))
  : maximum n pred :=
by
  obtain ⟨m, h_m⟩ := h_upper_max.left
  have : ¬ m > n := by grind
  grind

/--
  (upper pred0)を計算する関数predについて二分探索を行えば、
  pred0を満たす最大値を計算できる、という定理。
-/
theorem binarySearchForNonmonotone
  (pred0 : Nat → Prop)
  (pred : Nat → Bool)
  (h_pred : ∀ n, pred n = true ↔ upper pred0 n)
  (left : Nat) (right : Nat)
  (h_left : pred left = true)
  (h_right : pred right = false)
  : maximum (binarySearch pred left right) pred0 :=
by
  apply upperMaximumIsMaximum
  grind [binarySearchIsValid]

/--
  スコアは元のようかんの長さで上から押さえられるという定理。
-/
theorem scoreRecUpperBound (a0 : Nat) (a : List Nat) (l : Nat)
  : List.Chain (α := Nat) (· < ·) a0 (a ++ [l])
  → scoreRec a0 a l <= l - a0 :=
by
  fun_induction scoreRec with (simp <;> try grind)

/--
  ようかんを左に延ばしても、切れ目と右端が同じならスコアは減らないという定理。
-/
theorem scoreRecAntiMonotone (a00 : Nat) (a0 : Nat) (a : List Nat) (l : Nat)
  : a00 <= a0 → scoreRec a00 a l >= scoreRec a0 a l :=
by
  fun_induction scoreRec a00 a l with grind [scoreRec]

/--
  貪欲スコア判定関数は、0を与えればtrueを返すという定理。
-/
theorem betterScoreAchievableRecZeroCase (a0 : Nat) (a : List Nat) (l len : Nat)
  : len <= a.length → betterScoreAchievableRec a0 a l len 0 = true :=
by
  fun_induction betterScoreAchievableRec with grind

/--
  貪欲スコア判定関数は、lより大きい数を与えればfalseを返すという定理。
-/
theorem betterScoreAchievableRecMaxCase (a0 : Nat) (a : List Nat) (l len score : Nat)
  : score > l → betterScoreAchievableRec a0 a l len score = false :=
by
  fun_induction betterScoreAchievableRec with grind

/--
  貪欲法で、実際に切る場所のリストを計算する関数。

  実行時には呼び出されないが、「貪欲法で達成可能とされたスコア閾値は実際に達成できる」ということの、
  定式化や証明に必要になる。
-/
def betterScoreAchievingExample (a0 : Nat) (a : List Nat) (l len score : Nat) : List Nat :=
  if len == 0 then
    []
  else
    match a with
    | [] => []
    | a1 :: as =>
      if a1 - a0 >= score then
        a1 :: betterScoreAchievingExample a1 as l (len - 1) score
      else
        betterScoreAchievingExample a0 as l len score

/--
  上の関数が、実際に与えられた以上のスコアを出すという定理。
-/
theorem betterScoreAchievingExampleValid (a0 : Nat) (a : List Nat) (l len score : Nat)
  : betterScoreAchievableRec a0 a l len score = true
    → List.Sublist (betterScoreAchievingExample a0 a l len score) a
    ∧ (betterScoreAchievingExample a0 a l len score).length = len
    ∧ scoreRec a0 (betterScoreAchievingExample a0 a l len score) l >= score :=
by
  fun_induction betterScoreAchievableRec with (unfold betterScoreAchievingExample; grind)

/--
  貪欲法による判定は「健全」であるという定理。

  すなわち、貪欲法で達成可能とされたスコア閾値は実際に達成可能になるということ。
-/
theorem betterScoreAchievableSound (input : ProblemInput) (score : Nat)
  : betterScoreAchievable input score = true → upper (scoreAchievable input) score :=
by
  intro a
  exists scoreRec 0 (betterScoreAchievingExample 0 input.a input.l input.k score) input.l
  have h := betterScoreAchievingExampleValid 0 input.a input.l input.k score a
  grind

/--
  任意の切り方を与えられた際、それを貪欲法による結果に作り替える関数。

  実行時には呼び出されないが、「達成できるスコア閾値は貪欲法で達成可能と判定される」ということを
  証明する際、数学的帰納法での帰着先を示すガイドになる。
-/
def modifyToGreedySolution (a0 : Nat) (a : List Nat) (l score : Nat) (b : List Nat) : List Nat :=
  match b with
  | [] => []
  | _ :: bs =>
    match a with
    | [] => []
    | a1 :: as =>
      if a1 - a0 >= score then
        a1 :: modifyToGreedySolution a1 as l score bs
      else
        modifyToGreedySolution a0 as l score b

/--
  「達成できるスコア閾値は貪欲法で達成可能と判定される」という定理を、
  帰納法で示すために一般化された形。
-/
theorem betterScoreAchievableRecComplete (a0 : Nat) (a : List Nat) (l score : Nat) (b : List Nat)
  : scoreAchievablePartialBy a0 a l b.length (scoreRec a0 b l) b
  ∧ scoreRec a0 b l >= score
  ∧ List.Chain (· < ·) a0 (a ++ [l])
  → betterScoreAchievableRec a0 a l (b.length) score = true :=
by
  fun_induction modifyToGreedySolution a0 a l score b
  case case1 =>
    unfold betterScoreAchievableRec
    grind
  case case2 =>
    unfold betterScoreAchievableRec
    simp
  case case3 a0 b1 bs a1 as h_if ih =>
    intro h_pre
    obtain ⟨⟨h_sublist, _, _⟩, h_scoreRec, h_chain⟩ := h_pre
    cases h_chain
    case cons h_chain_2 =>
      unfold betterScoreAchievableRec
      simp [h_if]
      apply ih
      simp
      have a1b1 : a1 <= b1 := by
        cases h_sublist
        case cons =>
          have h_sublist_2 : (b1 :: bs).Sublist (as ++ [l]) := by grind
          obtain h := List.Chain.sublist h_chain_2 h_sublist_2
          cases h
          case cons => grind
        case cons₂ => grind
      simp_all
      obtain h_ineq := scoreRecAntiMonotone a1 b1 bs l a1b1
      grind
  case case4 a1 as _ _ =>
    intro h_pre
    obtain ⟨_, _, h_chain⟩ := h_pre
    simp
    have h_sublist_2 : (as ++ [l]).Sublist (a1 :: as ++ [l]) := by grind
    have := List.Chain.sublist h_chain h_sublist_2
    grind [Nat.le_min, betterScoreAchievableRec]

/--
  貪欲法による判定は「完全」であるという定理。

  すなわち、実際に達成可能なスコア閾値は貪欲法でも達成可能と判定されるということ。
-/
theorem betterScoreAchievableComplete (input : ProblemInput) (score : Nat)
  : upper (scoreAchievable input) score → betterScoreAchievable input score = true :=
by
  intro h_u
  obtain ⟨s, _, b, h3⟩ := h_u
  have : List.Chain (· < ·) 0 (input.a ++ [input.l]) := input.cond_al
  unfold scoreAchievableBy at h3
  unfold betterScoreAchievable
  obtain h_eq_len := h3.right.left
  rw [← h_eq_len]
  apply betterScoreAchievableRecComplete 0 input.a input.l score b
  grind

/--
  貪欲法による判定は正当であるという定理。
-/
theorem betterScoreAchievableIsValid (input : ProblemInput) (score : Nat)
  : upper (scoreAchievable input) score ↔ betterScoreAchievable input score = true :=
by
  constructor
  apply betterScoreAchievableComplete
  apply betterScoreAchievableSound

/--
  解法は正当であるという定理。

  これが証明したいことであった。
-/
theorem thmSolutionIsValid
  : abbrevSolutionIsValid solve :=
by
  intro input
  apply binarySearchForNonmonotone
  case h_pred =>
    intro
    apply Iff.symm
    apply betterScoreAchievableIsValid
  case h_left =>
    unfold betterScoreAchievable
    apply betterScoreAchievableRecZeroCase
    have : input.k <= input.n := input.cond_kn
    have : input.a.length = input.n := input.cond_an
    grind
  case h_right =>
    unfold betterScoreAchievable
    apply betterScoreAchievableRecMaxCase
    grind



/-
  TODO

  - maximumやupperあたりを、Mathlib.Order.UpperLower.Closureとかを使う形に書き直す
-/
