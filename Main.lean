/-
  競プロ典型90問1日目「Yokan Party」の検証済み解答
  問題設定・解答プログラム・正当性証明 の順に示す
-/

import Mathlib.Data.List.Chain

/-
  ==================問題設定==================
-/

/-
  入力と条件

  多くの定理証明支援系では、「命題Pの証明h」は「型Pに属する項h」と同一視される。
  Leanではさらに、関数の定義内でも項として証明が必要になることがある
  (典型的なのは配列などの添え字アクセス)。
  そこで入力データとそれらが満たす条件はここでは一緒に扱うことにする。

  数列についての不等式条件を表すのに List.Chain (Mathlib.Data.List.Chain より)を用いた。
-/
structure ProblemInput where
  n : Nat
  cond_n : n <= 100_000
  k : Nat
  cond_k : 1 <= k
  cond_kn : k <= n
  a : List Nat
  cond_an : a.length = n
  l : Nat
  cond_al : List.Chain (α := Nat) (· < ·) 0 (a ++ [l])

/-
  a0からlの座標を占めるようかんの切れ端を、aの各座標で切ったときの、ようかんの最小サイズ。

  後に備えて、再帰的に定義しておく。
  なお、Leanで再帰関数を定義すると、自動的に「必ず有限の回数で停止する」ことを示そうとする。
  明示的にその根拠を与えることもできる。
  根拠を明示せず、自動証明もできない場合、エラーとなって定義はできない。
  partialキーワードでこれを回避することもできるが、
  その場合はその関数についての性質の証明はほぼ不可能になる。
-/
@[grind]
def scoreRec (a0 : Nat) (a : List Nat) (l : Nat) :=
  match a with
  | [] => l - a0
  | a1 :: as => min (a1 - a0) (scoreRec a1 as l)

/-
  「a0からlの座標を占めるようかんを、aから選んだlen箇所の位置bで切ることで、
  スコアscoreが実現する」

  scoreRecに合わせて、一般化した形で定義しておく。
-/
abbrev scoreAchievablePartialBy (a0 : Nat) (a : List Nat) (l len score : Nat) (b : List Nat) : Prop :=
  List.Sublist b a
  ∧ b.length = len
  ∧ scoreRec a0 b l = score

/-
  「inputのもとで、bの各座標で切ればスコアsが実現する」
-/
abbrev scoreAchievableBy (input : ProblemInput) (b : List Nat) (s : Nat) : Prop :=
  scoreAchievablePartialBy 0 input.a input.l input.k s b

/-
  「inputのもとでスコアsが実現可能である」
-/
abbrev scoreAchievable (input : ProblemInput) (s : Nat) : Prop :=
  ∃ b, scoreAchievableBy input b s

/-
  「nはpredを満たす最大の自然数である」
-/
abbrev maximum (n : Nat) (pred : Nat → Prop) : Prop :=
  pred n ∧ ∀ m, (m > n) → ¬ pred m

/-
  「解答が正当である」

  すなわち、solutionにinputを与えて計算させたスコアsが、
  「inputのもとでスコアsが実現可能である」を満たす最大のsである。

  以下ではこのsolutionに入れるべきsolve関数を与え、
  thmSolutionIsValidでこれを証明する。
-/
abbrev abbrevSolutionIsValid (input : ProblemInput) (solution : ProblemInput → Nat) :=
  maximum (solution input) (scoreAchievable input)

/-
  ==================解答プログラム==================
-/

/-
  二分探索を行い、predがtrueからfalseに変わる点をleftとrightの間で探す。

  再帰の形になっているが、「末尾再帰最適化」(tail-call optimization)
  と呼ばれる機構によりループにコンパイルされるので、
  コールスタックを大きく消費する心配はない。
  一方で、定義が再帰の形になっていることで、性質の証明は行いやすくなる。
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

/-
  「a0からlの座標を占めるようかんを、aから選んだlen箇所で切ることで、
  score以上のスコアが実現できるか」を貪欲法で判定する。

  こちらも末尾再帰になっている。
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

/-
  「inputのもとで、score以上のスコアが実現できるか？」を貪欲法で判定する。
-/
def betterScoreAchievable (input : ProblemInput) (score : Nat) : Bool :=
  betterScoreAchievableRec 0 input.a input.l input.k score

/-
  貪欲法によるスコア上界の判定と二分探索を組み合わせ、最大スコアを求める。

  この関数の正当性が今回の目標になる。
-/
def solve (input : ProblemInput) : Nat :=
  binarySearch (betterScoreAchievable input) 0 (input.l + 1)

/-
  エントリーポイント。

  IOというのはHaskellなどにも登場する「IOモナド」で、
  この関数がデータの計算以外に入出力という副作用を持つことを示す。
  doという表記の役割もHaskellのものと同様。

  標準入力をパースしてsolveに与え、出力をprintするのに加え、
  問題の条件に入力が合っているかも判定している。
  ここで使われている
    if cond : x > y then ...
  という表記は dependent if-then-else と呼ばれ、
  then節内では変数condには「その条件が成り立つことの証明」が束縛される
  (命題の証明とは型を持つ項であることを思い出してほしい)。
  今回はelse節側がメインで、条件が成り立たないことの証明が得られる。
  Leanにおける項と証明の絡み合いの一つの形が見える。
-/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let instr ← stdin.readToEnd
  let intokens := (instr.split (·.isWhitespace)).toArray
  let n := intokens[0]!.trim.toNat!
  if cond_n : n > 100_000 then unreachable! else
  let l := intokens[1]!.trim.toNat!
  let k := intokens[2]!.trim.toNat!
  if cond_k : k < 1 then unreachable! else
  if cond_kn : k > n then unreachable! else
  let a := List.ofFn (n := n) fun i =>
    intokens[i.val + 3]!.trim.toNat!
  -- TODO: この仮定は人工的に与えなくてすむはず
  if cond_an : a.length != n then unreachable! else
  if cond_al : ¬ List.Chain (α := Nat) (· < ·) 0 (a ++ [l]) then unreachable! else
  let input : ProblemInput := {
    n := n
    cond_n := by grind
    k := k
    cond_k := by grind
    cond_kn := by grind
    a := a
    cond_an := by grind
    l := l
    cond_al := by grind
  }
  let solution := solve input
  IO.println s!"{solution}"

/-
  ==================正当性証明==================
-/

/-
  「predは"単調減少"である」

  すなわち、trueであるような自然数の集合は下に閉じている。
  標準ライブラリにあるので移行したい。
-/
abbrev monotone (pred : Nat → Prop) : Prop :=
  ∀ m n, (m <= n) → pred n → pred m

/-
  二分探索が正当であることの証明。

  多くの定理証明支援系では、タクティクと呼ばれるコマンドを繰り返して証明を行う。
  Leanではbyキーワードによりタクティクの列が開始される。

  ここではまず fun_induction タクティクを用いて、
  関数の再帰呼び出しの流れに沿った帰納法で証明を行う。
  関数の再帰は必ずいつか止まることが内部的に自動で示されているので、
  このタクティクでは内部的にそれを利用することになる。

  本来は各ベースケース・再帰呼び出しケースで証明を進める必要があるが、
  今回は with grind とし、「各ケースでgrindを使え」と指示した。
  grind タクティクはSMTソルバーの技法にヒントを得て作られた自動証明タクティクである。
  Leanプロジェクトを立ち上げたのがSMTソルバー「Z3」の開発者であったことも考えると、
  grindはある意味Leanの看板タクティクかもしれない。
  実際、今回の証明くらいならすぐに終わらせられるくらいには強力。

  二分探索を成り立たせるための仮定はここで前提条件として置いたが、
  プログラム側の引数にすることもできるだろう。
-/
theorem binarySearchIsValid
  (pred : Nat → Bool) (left : Nat) (right : Nat)
  (h_monotone : monotone (pred · = true))
  (h_left : pred left = true)
  (h_right : pred right = false)
  : maximum (binarySearch pred left right) (pred · = true) :=
by
  fun_induction binarySearch with grind

/-
  「n以上の数でpredが成り立つようなものが存在する」
-/
abbrev upper (pred : Nat → Prop) (n : Nat) : Prop :=
  ∃ m, m >= n ∧ pred m

theorem upperMaximumIsMaximum
  (n : Nat)
  (pred : Nat → Prop)
  (h_upper_max : maximum n (upper pred))
  : maximum n pred :=
by
  obtain ⟨m, h_m⟩ := h_upper_max.left
  have : ¬ m > n := by grind
  grind

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

theorem scoreRecUpperBound (a0 : Nat) (a : List Nat) (l : Nat)
  : List.Chain (α := Nat) (· < ·) a0 (a ++ [l])
  → scoreRec a0 a l <= l - a0 :=
by
  fun_induction scoreRec with (simp <;> try grind)

theorem scoreRecAntiMonotone (a00 : Nat) (a0 : Nat) (a : List Nat) (l : Nat)
  : a00 <= a0 → scoreRec a00 a l >= scoreRec a0 a l :=
by
  fun_induction scoreRec a00 a l with grind [scoreRec]

theorem betterScoreAchievableRecZeroCase (a0 : Nat) (a : List Nat) (l len : Nat)
  : len <= a.length → betterScoreAchievableRec a0 a l len 0 = true :=
by
  fun_induction betterScoreAchievableRec with grind

theorem betterScoreAchievableRecMaxCase (a0 : Nat) (a : List Nat) (l len score : Nat)
  : score > l → betterScoreAchievableRec a0 a l len score = false :=
by
  fun_induction betterScoreAchievableRec with grind

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

theorem betterScoreAchievingExampleValid (a0 : Nat) (a : List Nat) (l len score : Nat)
  : betterScoreAchievableRec a0 a l len score = true
    → List.Sublist (betterScoreAchievingExample a0 a l len score) a
    ∧ (betterScoreAchievingExample a0 a l len score).length = len
    ∧ scoreRec a0 (betterScoreAchievingExample a0 a l len score) l >= score :=
by
  fun_induction betterScoreAchievableRec with (unfold betterScoreAchievingExample; grind)

theorem betterScoreAchievableSound (input : ProblemInput) (score : Nat)
  : betterScoreAchievable input score = true → upper (scoreAchievable input) score :=
by
  intro a
  exists scoreRec 0 (betterScoreAchievingExample 0 input.a input.l input.k score) input.l
  have h := betterScoreAchievingExampleValid 0 input.a input.l input.k score a
  grind

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

theorem betterScoreAchievableRecCompleteWithGuide (a0 : Nat) (a : List Nat) (l score : Nat) (b : List Nat)
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

theorem betterScoreAchievableRecComplete (a0 : Nat) (a : List Nat) (l len score s : Nat)
  (b : List Nat)
  : scoreAchievablePartialBy a0 a l len s b
  ∧ s >= score
  ∧ List.Chain (· < ·) a0 (a ++ [l])
  → betterScoreAchievableRec a0 a l len score = true :=
by
  intro h_pre
  obtain h_eq_len := h_pre.left.right.left
  rw [← h_eq_len]
  apply betterScoreAchievableRecCompleteWithGuide a0 a l score b
  grind

theorem betterScoreAchievableComplete (input : ProblemInput) (score : Nat)
  : upper (scoreAchievable input) score → betterScoreAchievable input score = true :=
by
  intro h_u
  obtain ⟨s, _, b, h3⟩ := h_u
  have : List.Chain (· < ·) 0 (input.a ++ [input.l]) := input.cond_al
  unfold scoreAchievableBy at h3
  unfold betterScoreAchievable
  apply betterScoreAchievableRecComplete 0 input.a input.l input.k score s b
  grind

theorem betterScoreAchievableIsValid (input : ProblemInput) (score : Nat)
  : upper (scoreAchievable input) score ↔ betterScoreAchievable input score = true :=
by
  constructor
  apply betterScoreAchievableComplete
  apply betterScoreAchievableSound

theorem thmSolutionIsValid (input : ProblemInput)
  : abbrevSolutionIsValid input solve :=
by
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

  - Leanのdoc commentの書き方をちゃんと調べてそれに合わせる
  - maximumやupperあたりを、Mathlib.Order.UpperLower.Closureとかを使う形に書き直す
-/
