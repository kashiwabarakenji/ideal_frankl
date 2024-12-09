--主な内容は、IdealFamilyがIntersectionClosedFamilyであることの証明。

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Mathlib.Order.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sups
import Mathlib.Init.Data.Nat.Lemmas
import Init.Data.Int.Lemmas
import Init.Data.Nat.Lemmas
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import LeanCopilot
--import Mathlib.Data.Set.Basic
open Finset

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α]

-- IdealFamily が冪集合族かどうかをチェックする関数
noncomputable def isPowerSet {α : Type} [DecidableEq α] [Fintype α] (family : IdealFamily α) : Prop :=
   (Finset.powerset family.ground).toSet ⊆ {H : Finset α | family.toSetFamily.sets H}

-- IdealFamilyかどうかをチェックする関数
def isIdealFamily (α : Type) [DecidableEq α ] [Fintype α ] (F: SetFamily α ) : Prop :=
  (F.sets ∅) ∧              -- Empty set is included
  (F.sets F.ground) ∧       -- Ground set is included
  (∀ A B : Finset α, F.sets B → B ≠ F.ground → A ⊆ B → F.sets A)  -- Downward closure condition

def isIntersectionClosedFamily {α: Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) : Prop :=
    --family.sets  Finset (Finset U),-- Finset.univ ∈ sets ∧
    (∀ {s t : Finset α}, F.sets s→ F.sets t→  F.sets (s ∩ t))


--#check @isIntersectionClosedFamily
-- IdealFamilyがIntersectionClosedFamilyであることの定理
theorem idealFamily_is_intersectionClosed {α : Type} [DecidableEq α] [Fintype α] (family : IdealFamily α) :
  isIntersectionClosedFamily family :=
  by
  --sets := family.sets,
  --has_univ := family.has_univ,
  --intersection_closed := by
    unfold isIntersectionClosedFamily
    intros s t hs ht
    match Decidable.em (s = family.ground) with
    | Or.inl hsu =>
      rw [hsu]
      have tinc: t ⊆ family.ground := family.inc_ground t ht
      have h_inter_subset_t : family.ground ∩ t = t := by
         exact (Finset.inter_eq_right.mpr tinc)
      rw [h_inter_subset_t]
      exact ht

    | Or.inr hsu =>
      match Decidable.em (t =  family.ground) with
      | Or.inl htu =>
          rw [htu,Finset.inter_comm];
          have sinc: s ⊆ family.ground := family.inc_ground s hs
          have h_inter_subset_s : family.ground ∩ s = s := by
            exact (Finset.inter_eq_right.mpr sinc)
          rw [h_inter_subset_s]
          exact hs
      | Or.inr _ =>
        have h_inter_subset_s : s ∩ t ⊆ s := @Finset.inter_subset_left _ _ s t
        have h_downward_closed := family.down_closed (s ∩ t) s hs hsu h_inter_subset_s
        exact h_downward_closed --goal ⊢ family.sets (s ∩ t)

-- 具体的な有限台集合を定義
def example_U : Finset ℕ := List.toFinset [0, 1, 2]

-- ℕの部分集合のFintypeインスタンス
instance : Fintype {x // x ∈ example_U} :=
{
  elems := example_U.attach,
  complete := λ x => by simp
}

-- IdealFamily の具体例の sets を定義
def example_ideal_family2_sets : Finset (Finset {x // x ∈ example_U}) :=
  { example_U.attach,
    Finset.univ,
    Finset.filter (λ x=> x.val = 0 ∨ x.val = 1) Finset.univ,
    Finset.filter (λ x=> x.val = 0) Finset.univ,
    Finset.filter (λ x=> x.val = 1) Finset.univ,
    (∅ : Finset {x // x ∈ example_U}) }

-- example_ideal_family2 に空集合が含まれていることを示す補題
lemma empty_mem_example_ideal_family2_sets : (∅ : Finset {x // x ∈ example_U}) ∈ example_ideal_family2_sets :=
by
  apply Finset.mem_insert.mpr
  right
  apply Finset.mem_insert.mpr
  right
  apply Finset.mem_insert.mpr
  right
  apply Finset.mem_insert.mpr
  right
  apply Finset.mem_insert.mpr
  right
  exact Finset.mem_singleton_self _

def isAbundant {α : Type} [DecidableEq α] [Fintype α] (family : SetFamily α) (x : α) : Prop :=
  let hyperedges := Finset.filter (λ A => family.sets A = true) (family.ground.powerset)
  let countContainsX := (hyperedges.filter (λ e => x ∈ e)).card
  let countNotContainsX := (hyperedges.filter (λ e => x ∉ e)).card
  countContainsX > countNotContainsX

def isRare {α : Type} [DecidableEq α] [Fintype α] (family : SetFamily α) (x : α) : Prop :=
  ¬ isAbundant family x

-- {x, y}を含む集合族の要素の数が、{x, y}とdisjointな集合族の要素の数よりも真に大きいことを定義
def pair_superior {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (x y : α) : Prop :=
  let pair := ({x, y} : Finset α)
  let contains_pair := (F.ground.powerset).filter (λ A => F.sets A = true ∧ pair ⊆ A)
  let disjoint_pair := (F.ground.powerset).filter (λ B => F.sets B = true ∧ {x, y} ∩ B = ∅)
  contains_pair.card > disjoint_pair.card

-- 使用例
--example {U : Type} [DecidableEq U] [Fintype U] (F : SetFamily U) (x y : U) (hxy: x ≠ y) :
--  Prop :=
--  pair_superior F x y

-- {x, y}を含む集合族の要素の数が、{x, y}とdisjointな集合族の要素の数よりも真に大きいことを定義 def pair_superior {U : Type} [DecidableEq U] [Fintype U] (F : SetFamily U) (x y : U) (hxy : x ≠ y) : Prop := let pair := ({x, y} : Finset U) in let contains_pair := F.sets.filter (λ A, pair ⊆ A) in let disjoint_pair := F.sets.filter (λ B, disjoint pair B) in contains_pair.card > disjoint_pair.card -- 使用例 example {U : Type} [DecidableEq U] [Fintype U] (F : SetFamily U) (x y : U) (hxy : x ≠ y) : Prop := pair_superior F x y hxy -- ペア優位（pair superior）の定義 def pairSuperior (U : Type) [DecidableEq U] [Fintype U] (family : SetFamily U) (x y : U) : Bool := let hyperedges := family.sets let countContainsPair := (hyperedges.filter (λ e => {x, y} ⊆ e)).card let countDisjointPair := (hyperedges.filter (λ e => finsetDisjoint e ({x, y} : Finset U))).card countContainsPair > countDisjointPair
--===============
-- 集合族の中で最も大きい要素の大きさを返す関数
def max_card {α : Type} [DecidableEq α] [Fintype α] (S : Finset (Finset α)) : ℕ :=
  S.sup (λ s => s.card)
/-
-- 集合族から最大の要素だけを集める関数 使ってないかも。
def largest_elements {α : Type} [DecidableEq α] [Fintype α] (S : Finset (Finset α)) : Finset (Finset α) :=
  let max_card_val := max_card S
  S.filter (λ T => T.card = max_card_val)

-- 等式 使ってないかも。
lemma sup_image_eq_sup {α : Type} [DecidableEq α] [Fintype α] (S : Finset α) {f : α → ℕ} :
  (S.image f).sup id = S.sup f :=
  by
    rw [Finset.sup_image]
    congr
-/
/-
--対偶を示している。
omit [DecidableEq α] [Fintype α] in
lemma Finset.card_ne_zero_iff_nonempty (s : Finset α) : s.card ≠ 0 ↔ s ≠ ∅ :=
  by
    constructor
    · intro h
      contrapose! h
      exact Finset.card_eq_zero.mpr h
    · intro h
      contrapose! h
      exact Finset.card_eq_zero.mp h
-/

--exists_mem_of_subset_ne_oldの改良版。下で使っている。
--でも、大きい方の集合が全体集合の場合しか使えないので、さらに改良する必要があるかも。
omit [DecidableEq α] in
theorem exists_mem_of_subset_ne (H : Finset α) (h_ne : H ≠ Finset.univ) : ∃ x ∈ Finset.univ, x ∉ H :=
  by
    contrapose! h_ne -- H = U ならば、H ⊆ U であることになる
    ext x
    constructor --  x ∈ H → x ∈ Uと∀ x ∈ U, x ∈ Hにわける。
    · intro _ --使わない。
      exact mem_univ x
      ---∀ x ∈ U, x ∈ Hを示す。ゴールは、x in H。h_neそのもの？
    · intro hxU -- x in Uは仮定
      exact h_ne x hxU

-- 大きい方が全体集合でなくても使える形にした。これも使っている。BasicLemmaに移動してもよい。
omit [Fintype α] in
lemma exists_mem_of_card_gt (G G' : Finset α) (h : G.card > G'.card) : ∃ x ∈ G, x ∉ G' :=
  by
    -- Assume for contradiction that every element in G is also in G'
    by_contra h'
    -- This means that G is a subset of G'
    have subset_eq : G ⊆ G' :=
      by
        intro x hx
        -- If x ∈ G, then x ∉ G' would be false by assumption h'
        by_contra hx'
        apply h'
        use x
        --exact ⟨hx, hx'⟩
    -- By the pigeonhole principle, this implies that G.card ≤ G'.card, which contradicts h
    have card_le : G.card ≤ G'.card := card_le_card subset_eq
    exact not_le_of_gt h card_le --Nat.not_le_of_gt {n : Nat}  {m : Nat}  (h : n > m) :¬n ≤ m

--{hH : H = Finset.univ \ G}
--choose_two_pointsのなかで使っているが、使わないようにもできそう。
lemma H_neq_U (G: Finset α) (h : 0 < (Finset.univ \ G).card) : Finset.univ ≠ G :=
  by
    -- Assume for contradiction that Finset.univ = G
    intro h_eq
    -- Substitute Finset.univ for G in the hypothesis
    let H := Finset.univ \ G
    have hH : H = Finset.univ \ G := rfl
    have hH' : H = Finset.univ \ Finset.univ :=
      by
        rw [h_eq] at hH
        rw [h_eq]
        exact hH
    have card_univ : (Finset.univ : Finset α).card = Fintype.card α := Finset.card_univ
    have card_G : G.card = Fintype.card α := by rw [←h_eq, card_univ]
    have card_sdiff : (Finset.univ \ G).card = Fintype.card α - G.card := Finset.card_sdiff (Finset.subset_univ G)
    rw [←card_univ, card_G] at card_sdiff
    rw [Finset.sdiff_self] at hH'
    rw [←hH] at h
    rw [hH'] at h
    exact Nat.not_lt_zero 0 h

  -- 使ってない。
  omit [Fintype α] in
  lemma G_neq_G' (G G': Finset α)(h : 0 < (G' \ G).card) : G ≠ G' :=
  by
    -- Assume for contradiction that Finset.univ = G
    intro h_eq
    -- Substitute Finset.univ for G in the hypothesis
    let H := G' \ G
    have hH : H = G' \ G := rfl
    have hH' : H = G' \ G' :=
      by
        rw [h_eq] at hH
        exact hH

    rw [Finset.sdiff_self] at hH'
    rw [←hH] at h
    rw [hH'] at h
    exact Nat.not_lt_zero 0 h

-- choose_two_pointsのなかで使っている。
omit [Fintype α] in
lemma card_sdiff_singleton_ge_one (A : Finset α) (hA : 2 ≤ A.card) (x : α) (hx : x ∈ A) : 1 ≤ (A \ {x}).card :=
  by
    have h_card : (A.erase x).card = A.card - 1 :=
      by
        rw [Finset.card_erase_of_mem hx]
    -- Substitute the cardinality into the goal
    have h_eq : A.erase x = A \ {x} :=
      by
          rw [Finset.sdiff_singleton_eq_erase]
    rw [←h_eq,h_card]
    -- Since `A.card ≥ 2`, `A.card - 1` is at least 1
    exact Nat.sub_le_sub_right hA 1

--Gが全体集合より2点小さければ、Gに属さない2点を選べる
lemma choose_two_points {α : Type} [DecidableEq α] [Fintype α]
  (u2 : 2 ≤ Fintype.card α)(G : Finset α) (hG : G.card ≤ Fintype.card α- 2) :
  ∃ (x y :α), x ∈ Finset.univ \ G ∧ y ∈ Finset.univ \ G ∧ x ≠ y :=
  by
    let H := Finset.univ \ G
    have rH : H = Finset.univ \ G := rfl

    have gu : G.card ≤ Fintype.card α :=
    by
        apply Finset.card_le_univ
    have eq: G.card ≤ Fintype.card α - 2 ↔ 2 ≤ Fintype.card α - G.card :=
        by
          constructor

          intro h
          rw [Nat.le_sub_iff_add_le']
          rw [Nat.le_sub_iff_add_le] at h
          apply h
          apply u2 --この条件が難しかった。
          exact gu --この条件が難しかった。

          intro hxA
          rw [Nat.le_sub_iff_add_le]
          rw [Nat.le_sub_iff_add_le'] at hxA
          apply hxA
          apply gu
          exact u2
    have hH : 2 ≤ (H : Finset α).card := by
      rw [rH]
      rw [Finset.card_sdiff (Finset.subset_univ G)]
      apply eq.mp
      exact hG

    have hH_pos : 0 < (Finset.univ \ G).card := Nat.lt_of_lt_of_le zero_lt_two hH
    --A subseteq Gのときに、card(A) <= card(G)
    have H_nonempty := H_neq_U G hH_pos
    have mem_of_subset_neq := exists_mem_of_subset_ne G H_nonempty.symm --(ne_of_gt hH)
    obtain ⟨x, hxU, hxG⟩ := mem_of_subset_neq

    have u_minus_g:x ∈ Finset.univ \ G :=
      by
        rw [Finset.mem_sdiff]
        constructor
        exact hxU
        exact hxG

    have hH_pos' : 0 < ((Finset.univ \ G) \ {x}).card :=
      by
        apply Nat.lt_of_lt_of_le zero_lt_one
        apply card_sdiff_singleton_ge_one (Finset.univ \ G) hH
        exact u_minus_g
        --ここでのゴールは、1 ≤ ((univ \ G) \ {x}).card

    have gxx: x ∈ G ∪ {x} := by exact Finset.mem_union_right G (Finset.mem_singleton_self x)
    have ggg: G.card = (G ∪ {x}).card - 1 := by exact card_union_singleton_sub_one hxG gxx

    --Finset.sdiff_singleton_eq_eraseで実現できた可能性あり。
    have ugeex (G : Finset α) (x : α): (univ \ G).erase x = (univ \ G) \ {x}:=
      by
        ext y
        simp only [mem_erase, mem_univ, true_and, mem_singleton]
        constructor -- (univ \ G).erase xの要素であれば、(univ \ G) \ {x}の要素であることを示す。
        · intro h
          --#check h -- h : y ≠ x ∧ y ∈ univ \ G
          cases h with
          | intro h1 h2 =>
            apply Finset.mem_sdiff.mpr
            exact ⟨h2, ne_implies_not_mem_singleton x y h1⟩ --ここまでうまくいったっぽい。
        · intro h' -- goal y ≠ x ∧ y ∈ univ \ G
          --#check h' -- y ∈ (univ \ G) \ {x}
          rw [Finset.mem_sdiff] at h'
          --#check h' -- y ∈ univ \ G ∧ y ∉ {x}
          cases h' with
          | intro h1' h2' =>
            --#check h1' --h1 : y ∈ univ \ G
            --#check h2' --h2: y ≠ x
            exact ⟨not_mem_singleton_implies_ne h2', h1'⟩
    ----ugeexの証明がうまくいったっぽい


    have univ_sub_G_card : (Finset.univ \ G).card = Fintype.card α - G.card :=
      by
        rw [Finset.card_sdiff (Finset.subset_univ G)]
        exact rfl

    --lemma exists_mem_of_card_gt (G G' : Finset U) (h : G.card > G'.card) : ∃ x ∈ G, x ∉ G'
    --を用いて、U \ G \ x からyを取りたい。(U\{x}).cardとG.cardの大小関係を使う。
    have udxc_m_gc: (Finset.univ \ {x}).card > G.card :=
      by
        rw [Finset.sdiff_singleton_eq_erase]
        rw [ggg]
        rw [← card_union_singleton_sub_one hxG gxx]
        rw [←Finset.sdiff_singleton_eq_erase]
        rw [Finset.sdiff_singleton_eq_erase] at hH_pos'
        rw [ugeex] at hH_pos'
        have g_subset_ux: G ⊆ Finset.univ \ {x} :=
          by
            intro y
            intro hyG
            --#check hyG -- y ∈ G
            rw [Finset.mem_sdiff]
            constructor --どういう場合に分かれているかわからない。y in Finset.univ とy ¥notin {x}か。
            exact Finset.mem_univ y
            -- ここからはy ∉ {x} : Propを示す。x ∉ Gを使いそう。y in Gからx neq yがいえそう。
            have y_ne_x : y ≠ x :=
              by
                intro hH
                rw [hH] at hyG
                exact hxG hyG
            exact ne_implies_not_mem_singleton x y y_ne_x ---u_minus_g : x ∈ univ \ G
        ----ここまででg_subset_uxの証明が終わった。

        rw [diff_diff_eq_diff_diff (Finset.univ) G {x}] at hH_pos'
        --#check hH_pos' --hH_pos' : 0 < ((univ \ {x}) \ G).card
        have hh: ((univ \ {x}) \ G).card = (univ \ {x}).card - G.card := Finset.card_sdiff  g_subset_ux
        rw [hh] at hH_pos'
        exact Nat.lt_of_sub_pos hH_pos'
        ---udxc_m_gcの証明までうまくいったかも。

    obtain ⟨y, hyU, hyG⟩ := exists_mem_of_card_gt (Finset.univ \ {x}) G udxc_m_gc

    have ugyy: y ∈ Finset.univ \ G :=
      by
        rw [Finset.mem_sdiff]
        constructor
        --#check hyU -- y ∈ univ \ {x}
        rw [Finset.mem_sdiff] at hyU
        exact hyU.1
        exact hyG
    have x_ne_y : x ≠ y :=
      by
        intro hH
        have hyU2: y ∉ ({x} :Finset α):=
          by
            rw [Finset.mem_sdiff] at hyU
            --#check hyU
            exact hyU.2
        rw [mem_singleton] at hyU2
        rw [eq_comm] at hyU2
        --#check hyU2 -- ¬x = y
        exact hyU2 hH
    exact ⟨x, y, u_minus_g, ugyy, x_ne_y⟩
/-
--使ってない。
theorem Finset.univ_sdiff_univ : Finset.univ \ Finset.univ = (∅ : Finset α) :=
  Finset.sdiff_self Finset.univ

--使ってない。
theorem card_sdiff_univ (G : Finset α) : (Finset.univ \ G).card = Fintype.card α - G.card :=
  by
    -- Since Finset.univ is the universal set, G is a subset of Finset.univ
    -- Apply Finset.card_sdiff
    exact Finset.card_sdiff (Finset.subset_univ G)

--結果的に使ってない。
omit [DecidableEq α] in
lemma card_le_of_sub (G : Finset α) (u2 : 2 ≤ Fintype.card α) : (2 ≤ Fintype.card α - G.card) → (G.card ≤ Fintype.card α - 2) :=
  by
    intro h
    -- Rewrite the inequality using the lemma `Nat.le_sub_iff_add_le`
    rw [Nat.le_sub_iff_add_le] at h
    -- Use commutativity of addition to rearrange
    rw [add_comm] at h
    -- Now we can use the lemma again to rewrite the inequality back
    rw [Nat.le_sub_iff_add_le']
    -- The goal now follows directly from the assumption
    rw [add_comm 2 (G.card)]
    apply h
    apply u2
    have gu : G.card ≤ Fintype.card α :=
    by
        apply Finset.card_le_univ
    exact gu


omit [Fintype α] in
theorem exists_mem_of_subset_ne_old {U H : Finset α} (h_subset : H ⊆ U) (h_ne : H ≠ U) : ∃ x ∈ U, x ∉ H :=
  by
    contrapose! h_ne -- H = U ならば、H ⊆ U であることになる
    ext x
    constructor --  x ∈ H → x ∈ Uと∀ x ∈ U, x ∈ Hにわける。
    · intro hx
      by_contra hxU
      have : x ∈ U := h_subset hx
      simp [Finset.mem_of_subset] at this
      exact hxU this
      ---∀ x ∈ U, x ∈ Hを示す。ゴールは、x in H。h_neそのもの？
    · intro hxU -- x in Uは仮定
      exact h_ne x hxU

-/

end Ideal
