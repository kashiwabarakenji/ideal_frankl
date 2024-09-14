import LeanCopilot
import Mathlib.Tactic.ByContra
import Mathlib.Init.Data.Nat.Lemmas
--import Mathlib.Init.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.SymmDiff
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic

example {A:Prop} {B:Prop} {C:Prop} : (A → (B → C)) → (B → (A → C)) :=
  by
    intro hAB --goal : A → B → C
    intro hB --goal : A → C
    intro hA --goal : C
    exact (hAB hA) hB --カッコはなくても同じ


example {A:Prop} {B:Prop} : A → ((A → B) → B) :=
  by
    intro hA --goal : (A → B) → B
    intro hAB --goal : B
    exact hAB hA

example {A:Prop} {B:Prop} : (A → (A → B)) → (A → B) :=
  by
    intro hAAB --goal : A → B
    intro hA --goal : B
    exact (hAAB hA) hA --カッコはなくても同じ

example {A:Prop} {B:Prop} {C:Prop} : ((A ∧ B) → C) → (A → (B → C)) :=
  by
    intro hABC --goal : A → (B → C)
    intro hA --goal : B → C
    intro hB --goal : C
    exact hABC ⟨hA, hB⟩

example {A:Prop} {B:Prop} : A → (B → (A ∧ B)) :=
  by
    intro hA --goal : B → (A ∧ B)
    intro hB --goal : A ∧ B
    exact ⟨hA, hB⟩


  example {A B C D:Prop} : ((A → C) ∧ (B → D)) → ((A ∨ B) → (C ∨ D)):=
  by
    intro hACBD --goal : (A ∨ B) → (C ∨ D).    仮定hACBDの内容は ((A → C) ∧ (B → D))
    intro hAB --goal : C ∨ D.  仮定hABの内容は、 (A ∨ B)
    cases hAB with --ここで (A ∨ B) の左右で場合分け。withを使ったバージョン
    | inl hA => --左の場合。 hAにAが入る。｜は縦棒。
      exact Or.inl (hACBD.left hA) -- goal (C ∨ D)の左側Cを示す。
    | inr hB => --右の場合。 hBにBが入る。
      exact Or.inr (hACBD.right hB) -- goal (C ∨ D)の右側Dを示す。

example {A:Prop} {B:Prop} {C:Prop} : (A ∨ B → C) → (( A → C) ∧ (B → C)) :=
  by
    intro hABC --goal : (A → C) ∧ (B → C)
    constructor  --かつをそれぞれの場合に分ける。

    · intro hA --goal : C
      exact hABC (Or.inl hA)
    · intro hB --goal : C
      exact hABC (Or.inr hB)

example {A:Prop} {B:Prop} {C:Prop} : ((A → B) ∨ (A → C)) → (A → B ∨ C) :=
  by
    intro hABAC --goal : A → (B ∨ C)
    intro hA --goal : B ∨ C
    cases hABAC with
    | inl hAB => -- hAB : A → B
      exact Or.inl (hAB hA) --goalのB ∨ Cのうち、左側のBを示す。
    | inr hAC => -- hAC : A → C
      exact Or.inr (hAC hA)

example {A:Prop} {B:Prop} : (A → B) → (¬B → ¬A) :=
  by
    intro hAB --goal : ¬B → ¬A
    intro hNB --goal : ¬A
    intro hA --goal : False  hA:Aが仮定に加わる。
    exact hNB (hAB hA) -- 左が ¬B  右が B  これは矛盾

example {A:Prop} {B:Prop} : (A → ¬B) → (B → ¬A) :=
  by
    intro hANB --goal : B → ¬A
    intro hB --goal : ¬A
    intro hA --goal : False
    exact (hANB hA) hB

--Falseは常に偽である、証明できない命題
example {A:Prop}: (A → False) → ¬A := -- Falseとfalseは違う
  by
    intro hAF --goal : ¬A
    intro hA --goal : False
    exact hAF hA

example {A:Prop}: False ↔ (A ∧ ¬A) :=
  by
    apply Iff.intro --goalを両方向に2つに分解。
    · intro hF --goal : A ∧ ¬A
      cases hF
    · simp  -- 右から左への証明は簡単

example {A:Prop}: ¬¬A → A :=
  by
    intro hNNA --goal : A
    by_contra hA -- goal : False　排中律を利用している。import Mathlib.Tactic.ByContraが必要。
    exact hNNA hA -- hNNA : ¬¬A  hA : ¬A

example {A:Prop}: A→¬¬A := --この証明には排中律は必要ない。
  by
    intro hA --goal : ¬¬A
    intro hNA --goal : False --hNA : ¬A
    exact hNA hA -- hA : A

example (a: (A : Prop))  (b: (B :Prop)):(A ∧ B:Prop):=
by
  /- constructor -- goalはA ∧ B。「かつ」の証明を分岐。
  exact a -- 左側の証明が完了
  exact b -- 右側の証明が完了 -/
  exact ⟨a,b⟩ --両方同時に完了。(a,b)ではないので注意。

--- 述語論理

example : ∀ (x: Real),∃ (y :Real), x = y :=  -- Realとℝは同じ。実数全体の集合。
  by
    intro x --goal : ∃ (y : Real), x = y
    exact ⟨x, rfl⟩ -- rflは、両辺が等しいことを示す。

def my_prime (n : ℕ) : Prop :=
  n > 1 ∧ ∀ m : ℕ, m ∣ n → m = 1 ∨ m = n

example :∀ (x : ℝ), x*x ≥ 0 :=
  by
    intro x --goal : x * x ≥ 0
    exact (mul_self_nonneg x)

example {y : ℝ} : (∀(x : ℝ), x*x ≥ y*y) ↔ y = 0 :=
  by
    apply Iff.intro
    · intro h --goal : y ≥ 0
      simp_all only [ge_iff_le, le_refl]
      contrapose! h
      use 0
      simp_all only [mul_zero, mul_self_pos, ne_eq]
      simp_all only [not_false_eq_true]
    · intro h --goal : ∀ (x : ℝ), x * x ≥ y * y
      intro x --goal : x * x ≥ y * y
      subst h
      simp_all only [mul_zero, ge_iff_le]
      apply mul_self_nonneg

-- P(x)とは書かずに P xと書く。
example {α : Type} {P: α → Prop} {Q: α → Prop}: (∀ x : α, P x → Q x) → ((∀ x : α, P x) → (∀ x : α, Q x)) :=
  by --ここで　α　は型変数
    intro h1 h2 --h1 : ∀ (x : α), P x → Q x, h2 : ∀ (x : α), P x
    intro x
    apply h1
    apply h2

--上と同じ命題の証明を、ラムダ式で証明を書いたもの。
example {α : Type} {P: α → Prop} {Q: α → Prop}:
  (∀ x : α, P x → Q x) → ((∀ x : α, P x) → (∀ x : α, Q x)) := λ hPQ hP x => hPQ x (hP x)


example {α : Type} {P: α → Prop}: (∀x, (A → P x)) → (A → ∀x, P x) :=
  by
    intro a a_1 --a : ∀ (x : α), A → P x, a_1 : A
    intro x
    apply a
    exact a_1

--上と同じ命題の証明を、ラムダ式で証明を書いたもの。
example {α : Type} {P: α → Prop} {A: Prop}:
  (∀x, (A → P x)) → (A → ∀x, P x) := λ hAP hA x => hAP x hA

example {α : Type} {P: α → Prop}:  (A → ∀x, P x) → (∀x, (A → P x)) :=
  by
    intro a x a_1
    exact a a_1 x


--上と同じ命題の証明を、ラムダ式で証明を書いたもの。
example {α : Type} {P: α → Prop} {A: Prop}:
  (A → ∀x, P x) → (∀x, (A → P x)) := λ hA x hAx => hA hAx x

example {α : Type} {P: α → Prop}{A: Prop}:  (∀x, (A → P x)) → (A → ∀x, P x) :=
  by
    intro a a_1 x
    exact a x a_1


--上と同じ命題の証明を、ラムダ式で証明を書いたもの。
example {α : Type} {P: α → Prop} {A: Prop}:
  (∀x, (A → P x)) → (A → ∀x, P x) := λ hA hAx x => hA x hAx

example {α : Type} {P: α → Prop}{A: Prop}:  (A → ∀x, P x) → (∀x, (A → P x)) :=
  by
    intro a x a_1
    exact a a_1 x

--上と同じ命題の証明を、ラムダ式で証明を書いたもの。
example {α : Type} {P: α → Prop} {A: Prop}:
  (A → ∀x, P x) → (∀x, (A → P x)) := λ hA x hAx => hA hAx x

--スライド obtainを使う例。existsの中身を取り出す。
example {α : Type} {P: α → Prop} {Q: α → Prop}: (∀x,(P x → Q x)) → ((∃x, P x) → ∃x, Q x) :=
  by
    intro a a_1 --a : ∀ (x : α), P x → Q x, a_1 : ∃ (x : α), P x
    obtain ⟨w, h⟩ := a_1 --a1の中身をwとhに分解 a1 : ∃ (x : α), P x , w : α, h : P w
    exact ⟨w, a w h⟩ --a wは、P w → Q w

--スライド　useを使う例。existsの中身を与える。
example {α : Type} {P: α → Prop} {A: Prop}:(∃x,(A ∧ P x)) → (A ∧ ∃x,P x) :=
  by
    intro a
    obtain ⟨xx, h⟩ := a --h : A ∧ P x
    --cases' a with xx h  obtainの代わりにこっちでも良い。
    constructor
    exact h.1 -- A
    use xx -- exists　xとしてxxを使う。
    exact h.2 -- P xx

example {α : Type} {P: α → Prop} {A: Prop}: (A ∧ ∃x, P x) → ∃x, (A ∧ P x) :=
  by
    intro a
    obtain ⟨aa, h⟩ := a
    obtain ⟨x1, hh⟩ := h
    use x1

example {α : Type} {P: α → Prop}: ¬(∃x, P x) → ∀x,¬(P x) :=
  by
    intro a x
    rw [not_exists] at a  --そのまま利用しているのでずるいかも。
    exact a x

example {α : Type} {P: α → Prop}: (∀x, ¬P x) → (¬∃x, P x) :=
  by
    intro a
    rw [not_exists]
    exact a

example {α : Type} {P: α → Prop}: (¬∀x,P x) → ∃x,¬P x :=
  by
    intro a
    rw [not_forall] at a
    exact a

example {α : Type} {P: α → Prop}: (∃x,¬P x) → ¬∀x, P x :=
  by
    intro a
    rw [not_forall]
    exact a

--集合

-- 集合 A ⊆ B かつ B ⊆ C のとき、A ⊆ C であることを証明
example {α : Type} {A B C : Set α} : A ⊆ B → B ⊆ C → A ⊆ C :=
  by
    intros hAB hBC
    intro x
    intro hA
    apply hBC
    apply hAB
    exact hA

example {α : Type} (A B C : Set α) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
  by
    apply Set.ext -- goal: ∀ (x : α), x ∈ A ∪ B ∩ C ↔ x ∈ (A ∪ B) ∩ (A ∪ C)
    intro x -- goal: x ∈ A ∪ B ∩ C ↔ x ∈ (A ∪ B) ∩ (A ∪ C)
    apply Iff.intro -- 両方向に証明を分解
    -- A ∪ (B ∩ C) ⊆ (A ∪ B) ∩ (A ∪ C)の証明
    intro h -- h : x ∈ A ∪ (B ∩ C)
    cases h with
    | inl hA => -- hA : x ∈ Aのとき
      constructor
      . left; exact hA
      . left; exact hA
    | inr hBC => -- hBC : x ∈ B ∩ Cのとき
      constructor
      . right; exact hBC.1
      . right; exact hBC.2
    -- (A ∪ B) ∩ (A ∪ C) ⊆ A ∪ (B ∩ C)の証明
    intro h -- h : x ∈ (A ∪ B) ∩ (A ∪ C) -- goal: x ∈ A ∪ B ∩ C
    --simp only [Set.mem_inter_iff, Set.mem_union] 必要なかったのでコメントアウト。後で消す。
    obtain ⟨left, right⟩ := h -- left : x ∈ A ∪ B, right : x ∈ A ∪ C
    cases left with
    | inl h =>
      cases right with
      | inl h_1 =>
        exact Or.inl h
      | inr h_2 =>
        exact Or.inl h
    | inr h_1 =>
      cases right with
      | inl h =>
        exact Or.inl h
      | inr h_2 =>
        exact Or.inr ⟨h_1, h_2⟩

--simoを利用した証明の例
example {α : Type} (A B C : Set α) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
  by
    ext x
    --goal x ∈ A ∩ (B ∪ C) ↔ x ∈ A ∩ B ∪ A ∩ C
    simp only [Set.mem_inter_iff, Set.mem_union]
    -- Set.mem_inter_iff.{u} {α : Type u} (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b
    -- Set.mem_union.{u} {α : Type u} (x : α) (a b : Set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b
    --goal: x ∈ A ∧ (x ∈ B ∨ x ∈ C) ↔ x ∈ A ∧ x ∈ B ∨ x ∈ A ∧ x ∈ C
    --ここにtautoを入れると、その時点で証明が終わってしまう。
    apply Iff.intro
    · intro a
      cases a with
      | intro hA hBC => --hA : x ∈ A, hBC : x ∈ B ∨ x ∈ C
        cases hBC with
        | inl hB => --hB : x ∈ B
          exact Or.inl ⟨hA, hB⟩
        | inr hC => --hC : x ∈ C
          exact Or.inr ⟨hA, hC⟩
    · intro a
      cases a with
      | inl h => simp_all only [true_or, and_self] --constructorで分割しても良い。
      | inr h_1 => simp_all only [or_true, and_self]


example {α : Type} {A B C : Set α} : (A ⊆ B ∧ A ⊆ C) ↔ A ⊆ (B ∩ C) :=
  by
    apply Iff.intro
    -- (A ⊆ B ∧ A ⊆ C) → A ⊆ (B ∩ C)
    intro h
    intro x hA
    have hB := h.1 hA -- A ⊆ B から x ∈ B
    have hC := h.2 hA -- A ⊆ C から x ∈ C
    exact ⟨hB, hC⟩ -- よって x ∈ B ∩ C

    -- A ⊆ (B ∩ C) → (A ⊆ B ∧ A ⊆ C)
    intro h
    constructor
    -- A ⊆ B を証明
    intro x hA
    exact (h hA).1
    -- A ⊆ C を証明
    intro x hA
    exact (h hA).2

example {α : Type} {A B C : Set α} : (A ⊆ C ∧ B ⊆ C) ↔ A ∪ B ⊆ C :=
  by
    apply Iff.intro
    -- A ⊆ C ∧ B ⊆ C → A ∪ B ⊆ C
    intro h
    intro x
    intro hx
    cases hx with
    | inl hA => exact h.1 hA
    | inr hB => exact h.2 hB

    -- A ∪ B ⊆ C → A ⊆ C ∧ B ⊆ C
    intro h
    constructor
    -- A ⊆ C を証明
    intro x hA
    apply h
    exact Or.inl hA
    -- B ⊆ C を証明
    intro x hB
    apply h
    exact Or.inr hB

--既存の定理のrwの例で使える。
example {α : Type} {A B : Set α} : A ⊆ B ↔ Bᶜ ⊆ Aᶜ :=
  by
    apply Iff.intro
    -- goal: A ⊆ B → Bᶜ ⊆ Aᶜ
    intro h
    intro x
    intro hxB
    rw [Set.mem_compl_iff] --pᶜ ↔ ¬p
    tauto

    -- goal: Bᶜ ⊆ Aᶜ → A ⊆ B
    intro h
    intro x
    intro hxA
    by_contra hxB
    exact h hxB hxA

-- rwの例として使える。
example {α : Type} {A B : Set α} : A ⊆ B ↔ A ∩ B = A :=
  by
    apply Iff.intro
    -- A ⊆ B → A ∩ B = A
    intro h
    apply Set.ext -- goal: ∀ (x : α), x ∈ A ∩ B ↔ x ∈ A
    intro x -- goal: x ∈ A ∩ B ↔ x ∈ A
    apply Iff.intro
    -- goal: x ∈ A ∩ B → x ∈ A
    intro hAB
    exact hAB.1
    -- goal: x ∈ A → x ∈ A ∩ B
    intro hA
    exact ⟨hA, h hA⟩

    -- A ∩ B = A → A ⊆ B
    intro h
    intro x
    intro hA --goal : x ∈ B --hA: x ∈ A
    rw [← h] at hA -- hA : x ∈ A ∩ B
    exact hA.2

--上の言明の証明を既存の定理に帰着させた例。
example {α : Type} {A B : Set α} : A ⊆ B ↔ A ∩ B = A :=
by
  rw [Set.inter_eq_left]

-- 差集合は、　A \ Bという表記になる。A - Bではない。
example  {α : Type} {A B C: Set α}: A \ (B \ C)=(A \ B) ∪ (A ∩ C) :=
  by
    ext x
    simp only [Set.mem_diff, not_and, not_not, Set.mem_union, Set.mem_inter_iff] --全部必要。
    --Set.mem_diff Set.mem_diff.{u} {α : Type u} {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t
    --not_and {a b : Prop} : ¬(a ∧ b) ↔ a → ¬b
    -- goal x ∈ A ∧ (x ∈ B → x ∈ C) ↔ x ∈ A ∧ x ∉ B ∨ x ∈ A ∧ x ∈ C
    apply Iff.intro
    · intro a
      simp_all only [true_and]
      obtain ⟨_, right⟩ := a -- _はプレイスホルダー。その値は取り出してもつかわないので。
      by_cases h : x ∈ B
      -- ケース 1: x ∈ B の場合
      case pos =>
        right
        exact ‹x ∈ B → x ∈ C› h
      -- ケース 2: x ∉ B の場合
      case neg =>
        left
        exact h

    · intro a
      cases a with
      | inl h => simp_all only [false_implies, and_self]
      | inr h_1 => simp_all only [implies_true, and_self]

--上の言明の証明をtautoの計算に帰着させた例。
example {α : Type} {A B C : Set α} : A \ (B \ C) = (A \ B) ∪ (A ∩ C) :=
by
  ext x
  simp only [Set.mem_diff, not_and, not_not, Set.mem_union, Set.mem_inter_iff]
  tauto

example  {α : Type} {A B C: Set α}: (A ∪ B) \ C =(A \ C) ∪ (B \ C) :=
  by
    ext x
    simp only [Set.mem_diff, Set.mem_union]
    apply Iff.intro
    · intro a
      simp_all only [not_false_eq_true, and_true] --もっと細かく証明したい。
    · intro a
      cases a with
      | inl h => simp_all only [true_or, not_false_eq_true, and_self]
      | inr h_1 => simp_all only [or_true, not_false_eq_true, and_self]

--上の言明の証明をtautoの計算に帰着させた例。
example  {α : Type} {A B C: Set α}: (A ∪ B) \ C =(A \ C) ∪ (B \ C) :=
  by
    ext x
    simp only [Set.mem_diff, Set.mem_union]
    tauto

--the symmetric difference (△) operator
--import Mathlib.Order.SymmDiff
-- 対称差（symmDiff）を表す △ 演算子を定義
infixl:70 " ∆ " => symmDiff

-- A ∪ B = (A △ B) △ (A ∩ B) を示す
example {α : Type} (A B : Set α) : A ∪ B = (A ∆ B) ∆ (A ∩ B) :=
  by
    apply Set.ext
    intro x
    -- 両方向の証明
    apply Iff.intro

    -- A ∪ B ⊆ (A △ B) △ (A ∩ B)
    intro h
    cases h with
    | inl hA =>
      unfold symmDiff
      simp_all only [Set.sup_eq_union, Set.mem_union, Set.mem_diff, or_false, Set.mem_inter_iff]
      tauto

    | inr hB =>
      unfold symmDiff
      simp_all only [Set.sup_eq_union, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
      tauto

    -- (A △ B) △ (A ∩ B) ⊆ A ∪ B
    intro h
    unfold symmDiff at h
    simp_all only [Set.sup_eq_union, Set.mem_union, Set.mem_diff, Set.mem_inter_iff, not_and, not_or, not_not]
    cases h with
    | inl h_1 =>
      obtain ⟨left, _⟩ := h_1
      cases left with
      | inl h => simp_all only [not_false_eq_true, imp_self, or_false]
      | inr h_1 => simp_all only [not_true_eq_false, false_implies, or_true]
    | inr h_2 => simp_all only [or_self]

--- 写像

-- f : X → Y に対して、任意の A ⊆ B ⊆ X に対して f(A) ⊆ f(B) を示す。像はf''で表す。
-- haveが登場する例になっている。
example {X Y : Type} (f : X → Y) {A B : Set X} (h : A ⊆ B) : f '' A ⊆ f '' B :=
  by
    intro y
    -- ゴールは y ∈ f '' A → y ∈ f '' B
    intro hy --y ∈ f '' A
    cases hy with
    | intro x hx => -- hx : x ∈ A ∧ f x = y
      let fx_eq_y := hx.2
      -- fx_eq_y : f x = y
      have hB: x ∈ B := h hx.1
      let rst := Set.mem_image_of_mem f hB
      rw [fx_eq_y] at rst
      exact rst

-- f(A ∩ B) ⊆ f(A) ∩ f(B) を証明する
example {X Y : Type} (f : X → Y) (A B : Set X) : f '' (A ∩ B) ⊆ (f '' A) ∩ (f '' B) :=
  by
    intro y
    intro h
    -- y ∈ f(A ∩ B) を解釈
    cases h with
    | intro x hx =>
      let  fx_eq_y := hx.2
      -- hx : x ∈ A ∩ B, fx_eq_y : f x = y
      constructor
      -- f(x) ∈ f(A)
      cases hx.1 with
      | intro hA hB => --hA x ∈ A  hB : x ∈ B --goal y ∈ f '' A
        let rst := Set.mem_image_of_mem f hA
        rw [fx_eq_y] at rst
        exact rst
      -- f(x) ∈ f(B)
      cases hx.1 with
      | intro hA hB => --hA x ∈ A  hB : x ∈ B --goal y ∈ f '' A
        let rst := Set.mem_image_of_mem f hB
        rw [fx_eq_y] at rst
        exact rst

-- f(A ∪ B) = f(A) ∪ f(B) を証明
example {X Y : Type} (f : X → Y) (A B : Set X) : f '' (A ∪ B) = f '' A ∪ f '' B :=
  by
    apply Set.ext -- 集合の等式を示すために extensionality を使用
    intro y
    apply Iff.intro
    -- f(A ∪ B) ⊆ f(A) ∪ f(B)
    intro h
    cases h with
    | intro x hx  =>
      let fx_eq_y := hx.2
      cases hx.1 with
      | inl hA =>
        left
        exact ⟨x, hA, fx_eq_y⟩
      | inr hB =>
        right
        exact ⟨x, hB, fx_eq_y⟩

    -- f(A) ∪ f(B) ⊆ f(A ∪ B)
    intro h
    cases h with
    | inl hA =>
      cases hA with
      | intro x hxA =>
        let fx_eq_y := hxA.2
        exact ⟨x, Or.inl hxA.1, fx_eq_y⟩
    | inr hB =>
      cases hB with
      | intro x hxB =>
        let fx_eq_y := hxB.2
        exact ⟨x, Or.inr hxB.1, fx_eq_y⟩

-- 任意の A, B ⊆ Y に対して f^{-1}(A ∩ B) = f^{-1}(A) ∩ f^{-1}(B) を証明。ChatGPT-4そのまま通った。
example {X Y : Type} (f : X → Y) (A B : Set Y) : f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B :=
  by
    apply Set.ext -- 集合の等式を示すために外延性を使用
    intro x
    apply Iff.intro
    -- f⁻¹(A ∩ B) ⊆ f⁻¹(A) ∩ f⁻¹(B)
    intro h
    constructor
    -- f(x) ∈ A
    exact h.1
    -- f(x) ∈ B
    exact h.2

    -- f⁻¹(A) ∩ f⁻¹(B) ⊆ f⁻¹(A ∩ B)
    intro h
    exact ⟨h.1, h.2⟩

-- 任意の A, B ⊆ Y に対して f^{-1}(A ∪ B) = f^{-1}(A) ∪ f^{-1}(B) を証明
example {X Y : Type} (f : X → Y) (A B : Set Y) : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B :=
  by
    apply Set.ext -- 集合の等式を示すために外延性を使用
    intro x
    apply Iff.intro
    -- f⁻¹(A ∪ B) ⊆ f⁻¹(A) ∪ f⁻¹(B)
    intro h
    cases h with
    | inl hA =>
      left
      exact hA
    | inr hB =>
      right
      exact hB

    -- f⁻¹(A) ∪ f⁻¹(B) ⊆ f⁻¹(A ∪ B)
    intro h
    cases h with
    | inl hA =>
      exact Or.inl hA
    | inr hB =>
      exact Or.inr hB

lemma diff_empty {α : Type} {x₁ x₂ : α} (h : ¬(x₁ = x₂)) : {x₁} ∩ {x₂} = (∅ : Set α) :=
  by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro y
    intro hy
    cases hy with
    | intro hy₁ hy₂ =>
      apply h
      exact Eq.trans hy₁.symm hy₂

-- 任意の A, B ⊆ X について f(A ∩ B) = f(A) ∩ f(B) であることが、f が単射であることと同値であることを示す
example  {X Y : Type} (f : X → Y) :
  (∀ A B : Set X, f '' (A ∩ B) = f '' A ∩ f '' B) ↔ Function.Injective f :=
  by
    apply Iff.intro

    -- (→) 方向: f(A ∩ B) = f(A) ∩ f(B) → f が単射
    intro h_inj
    -- x₁, x₂ ∈ X に対して、f(x₁) = f(x₂) のとき、x₁ = x₂ を示す
    intro x₁ x₂ hfx
    -- A を {x₁}、B を {x₂} として交差に関する条件を考える
    have h := h_inj {x₁} {x₂}
    simp at h
    -- f({x₁}) = {f(x₁)} かつ f({x₂}) = {f(x₂)} より、仮定 f(x₁) = f(x₂) から同じ像が得られる
    have h₁ : f '' ({x₁} ∩ {x₂}) = {f x₁} := by
      simp_all only [Set.image_singleton, Set.inter_self]
    simp only [Set.image_singleton, Set.inter_self] at h₁
    by_contra conh
    have h3: f '' ({x₁} ∩ {x₂}) = (∅ : Set Y) := by
      rw[diff_empty conh]
      -- Set.image_singleton.{u_1, u_2} {α : Type u_1} {β : Type u_2} {f : α → β} {a : α} : f '' {a} = {f a}
      -- Set.image_empty.{u_1, u_2} {α : Type u_1} {β : Type u_2} (f : α → β) : f '' ∅ = ∅
      simp_all only [Set.image_singleton, Set.inter_self, ne_eq, Set.image_empty]

    -- Set.singleton_ne_empty.{u} {α : Type u} (a : α) : {a} ≠ ∅
    -- ne_eq.{u_1} {α : Sort u_1} (a b : α) : (a ≠ b) = ¬a = b
    -- goal False
    simp_all only [Set.image_singleton, Set.inter_self, ne_eq, Set.singleton_ne_empty]

    -- (←) 方向: f が単射 → f(A ∩ B) = f(A) ∩ f(B)
    intro hf
    -- 任意の A, B ⊆ X について、f(A ∩ B) ⊆ f(A) ∩ f(B) と f(A) ∩ f(B) ⊆ f(A ∩ B) を示す
    intros A B
    apply Set.ext --等価性を示すために外延性を使用
    intro y -- y ∈ f '' (A ∩ B) ↔ y ∈ f '' A ∩ f '' B
    apply Iff.intro -- 両方向に証明を分解

    -- f(A ∩ B) ⊆ f(A) ∩ f(B)
    intro h
    -- f '' (A ∩ B) に属する y が与えられたとき、それが f(A) ∩ f(B) にも属することを示す
    obtain ⟨x, hx1, hx2⟩ := h --hx1 : x ∈ A ∩ B, hx2 : f x = y
    constructor
    -- f(x) ∈ f(A)
    · exact ⟨x, hx1.1, hx2⟩
    -- f(x) ∈ f(B)
    · exact ⟨x, hx1.2, hx2⟩

    -- f(A) ∩ f(B) ⊆ f(A ∩ B)
    intro h
    -- f(A) と f(B) の共通部分にある y が f(A ∩ B) に属することを示す
    obtain ⟨a, haA, hfa⟩ := h.1 -- f a = y
    obtain ⟨b, hbB, hfb⟩ := h.2 -- f b = y
    have : f a = f b := by --rw [← hfa, ← hfb]
      subst hfa
      simp_all only [Set.mem_inter_iff, Set.mem_image]
    have : a = b := hf this
    subst this -- goal : y ∈ f '' (A ∩ B)
    exact ⟨a, ⟨haA, hbB⟩, hfa⟩

--別証明というほど違わないが、上と同じ言明をあらためて証明したもの。証明の流れは同じ。
example {X Y : Type} (f : X → Y) :
  (∀ A B : Set X, f '' (A ∩ B) = f '' A ∩ f '' B) ↔ Function.Injective f :=
by
  apply Iff.intro

  -- (→) direction: f(A ∩ B) = f(A) ∩ f(B) → f is injective
  intro h_inj
  intro x₁ x₂ hfx
  -- Consider A = {x₁}, B = {x₂} and use the given condition on intersections
  have h := h_inj {x₁} {x₂}
  simp only [Set.image_singleton, Set.inter_empty, Set.image_empty] at h
  -- From f(x₁) = f(x₂), we get the same image for both sets
  by_contra hne -- Goal False
  have : f '' ({x₁} ∩ {x₂}) = ∅ := by
    simp [hne]
    simp_all only [Set.image_singleton]
    tauto
  -- But f '' ({x₁} ∩ {x₂}) = {f x₁}, which leads to a contradiction
  simp_all only [Set.inter_self, Set.singleton_ne_empty]

  -- (←) direction: f is injective → f(A ∩ B) = f(A) ∩ f(B)
  intro hf
  intros A B
  apply Set.ext
  intro y
  apply Iff.intro

  -- f(A ∩ B) ⊆ f(A) ∩ f(B)
  intro h
  obtain ⟨x, hx, rfl⟩ := h --hx: x ∈ A ∩ B
  exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩

  -- f(A) ∩ f(B) ⊆ f(A ∩ B)
  intro h -- goal: y ∈ f '' (A ∩ B) -- h: y ∈ f '' A ∩ f '' B
  obtain ⟨a, haA, rfl⟩ := h.1
  obtain ⟨b, hbB, hfb⟩ := h.2 --  f b = f a
  have : a = b := by
    apply hf
    simp_all only
  subst this -- goal: f a ∈ f '' (A ∩ B)
  exact ⟨a, ⟨haA, hbB⟩, rfl⟩



--lean copilotを使った証明。このあとに短くした証明ものせる。
example {α β : Type}  (f : α → β) :
  (∀ A : Set α, (f '' A)ᶜ ⊆ f '' (Aᶜ)  ) ↔ Function.Surjective f :=
  by
    apply Iff.intro

    -- (→) 方向: f が全射なら f(A)^c ⊆ f(A^c) が成り立つことを示す
    -- 仮定: 任意の A に対して f(A^c) ⊆ (f(A))^c が成り立つ
    intro h
    rw [Function.Surjective]
    by_contra hns
    push_neg at hns
    obtain ⟨y, hy⟩ := hns
    have h1 : y ∈ (f '' Set.univ)ᶜ := by
      simp_all only [Set.image_subset_iff, Set.preimage_compl, Set.compl_subset_compl, ne_eq, Set.image_univ,
        Set.mem_compl_iff, Set.mem_range, exists_false, not_false_eq_true]
    have h2 : y ∉ f '' (Set.univᶜ) := by
      simp_all only [Set.image_subset_iff, Set.preimage_compl, Set.compl_subset_compl, ne_eq, Set.image_univ,
    Set.mem_compl_iff, Set.mem_range, exists_false, not_false_eq_true, Set.compl_univ, Set.image_empty,
    Set.mem_empty_iff_false]
    exact h2 (h Set.univ h1)


    -- (←) 方向: 任意の A ⊆ X について f(A)^c ⊆ f(A^c) ならば f が全射であることを示す
    intro h
    intro A
    -- y が Y の任意の要素とする
    -- A = ∅ とすると f(∅) = ∅ なので補集合を考える
    rw [Function.Surjective] at h

    --have sub0: X ⊆ Y ↔ Yᶜ ⊆ Xᶜ := by
    --  intro h
    --  rw [Set.subset_iff, Set.compl_subset_compl]
    --  exact h
    have sub1: (f '' A)ᶜ ⊆ f '' Aᶜ ↔ (f '' Aᶜ)ᶜ ⊆ (f '' A) := by
      apply Iff.intro
      intro h
      intro x hxA
      simp_all only [Set.mem_compl_iff, Set.mem_compl_iff]
      by_contra hnx
      let hnx2 :=(h hnx)
      contradiction

      intro h'
      intro x hxA
      simp_all only [Set.mem_compl_iff, Set.mem_compl_iff]
      by_contra hnx
      let hnx2 :=(h' hnx)
      contradiction

    rw [sub1]
    intro y
    -- 任意の y ∈ (f '' Aᶜ)ᶜ を取る
    intro hy
    -- y ∉ f '' Aᶜ であることを仮定
    simp at hy
    -- 全射性 hf により、ある x ∈ α が存在して f x = y となる
    obtain ⟨x, hx⟩ := h y
    -- ここで、y ∉ f '' Aᶜ なので、x ∉ Aᶜ すなわち x ∈ A
    by_contra hh
    -- x ∈ Aᶜ であると仮定すると矛盾
    subst hx
    simp_all only [Set.mem_image, not_exists, not_and]
    apply hy
    on_goal 2 => {apply Eq.refl
    }
    · apply Aesop.BuiltinRules.not_intro
      intro a
      apply hh
      · exact a
      · simp_all only

-- 別証明というわけでもないが、同じ定理の証明をふたたび書いてみる。
example {α β : Type}  (f : α → β) :
  (∀ A : Set α, (f '' A)ᶜ ⊆ f '' (Aᶜ)) ↔ Function.Surjective f :=
  by
    apply Iff.intro

    -- (→) 方向: f が全射なら f(A)^c ⊆ f(A^c) が成り立つことを示す
    -- 仮定: 任意の A に対して f(A^c) ⊆ (f(A))^c が成り立つ
    intro h
    rw [Function.Surjective]
    by_contra hns --背理法
    push_neg at hns
    obtain ⟨y, hy⟩ := hns

    -- f が全射ではないので、ある y ∈ β に対して f(x) = y となる x が存在しない
    -- このとき、y は f '' α に含まれないので y ∈ (f '' Set.univ)ᶜ となる
    -- Set.univは全体集合
    have hynot : y ∈ (f '' Set.univ)ᶜ := by
      simp_all only [Set.mem_compl_iff, Set.mem_range]
      --Set.mem_compl_iff:  a ∈ UpperSet.compl s ↔ a ∉ s
      --Set.mem_range  : x ∈ Set.range f ↔ ∃ y, f y = x
      simp [hy]

    -- 仮定より (f '' Set.univ)ᶜ ⊆ f '' (Set.univᶜ)
    specialize h Set.univ -- Set.univは全体集合
    -- Set.univᶜ は空集合なので、f '' (Set.univᶜ) = f '' ∅ = ∅
    rw [Set.compl_univ, Set.image_empty] at h
    --Set.compl_univ : Set.univᶜ = ∅

    -- よって (f '' Set.univ)ᶜ ⊆ ∅
    -- すると y ∈ ∅ となり矛盾が生じる
    exact Set.not_mem_empty y (h hynot)
    --a ∉ ∅

    -- (←) 方向: f(A)^c ⊆ f(A^c) なら f が全射であることを示す
    intro hsurj
    rw [Function.Surjective] at hsurj
    intros A x hx
    -- x が f(A)^c に属するという仮定のもとで、f が全射なら矛盾を導く
    rw [Set.mem_compl_iff, Set.mem_image] at hx
    --Set.mem_compl_iff:  a ∈ UpperSet.compl s ↔ a ∉ s
    --Set.mem_image:  y ∈ f '' s ↔ ∃ x ∈ s, f x = y
    --
    by_contra hns
    -- 存在しない元yを取得
    push_neg at hns
    obtain ⟨a, ha⟩ := hsurj x
    subst ha  --代入
    simp_all only [not_exists, not_and, Set.mem_image, Set.mem_compl_iff]
    --#check not_exists -- not_exists.{u_1} {α : Sort u_1} {p : α → Prop} : (¬∃ x, p x) ↔ ∀ (x : α), ¬p x
    --#check not_and -- not_and : ¬a ∧ ¬b ↔ ¬(a ∧ b)
    apply hns
    on_goal 2 => {apply Eq.refl
    }
    · intro h
      apply hx a
      simp_all only
      exact rfl

--単射と単射の合成は単射
example {A B C : Type} (f : A → B) (g : B → C)
  (hf : Function.Injective f) (hg : Function.Injective g) :
  Function.Injective (g ∘ f) := by
  -- 任意の x₁, x₂ ∈ A に対して g(f(x₁)) = g(f(x₂)) を仮定
  intros x₁ x₂ h
  -- g が単射なので、f(x₁) = f(x₂) を導く
  apply hf
  apply hg
  exact h

--全射と全射の合成は全射
example {A B C : Type} (f : A → B) (g : B → C)
  (hf : Function.Surjective f) (hg : Function.Surjective g) :
  Function.Surjective (g ∘ f) := by
  -- 任意の c ∈ C に対して、ある a ∈ A を見つける
  intro c
  -- g が全射なので、ある b ∈ B が存在して g(b) = c
  obtain ⟨b, hb⟩ := hg c
  -- f が全射なので、ある a ∈ A が存在して f(a) = b
  obtain ⟨a, ha⟩ := hf b
  -- 合成関数の値 g(f(a)) = c となる
  use a
  rw [Function.comp_apply, ha, hb]
