--newideal.leanをrefactoringしたものから台集合を変えたもの。
--全体集合をUを使っていたのをalphaに変えた。これが正しい使い方と思われる。
--このバージョンがIdeal集合族にrare vertexが存在する定理のメインバージョン。
--ideal-rareからさらにBasicDefinitionsを使うようにしたもの。

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset
--import Mathlib.Init.Function
import Init.SimpLemmas
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import LeanCopilot

namespace Ideal

--import Mathlib.Data.Subtype --Subtypeは使っているが、importしなくても大丈夫かも。
--Mathlib.Data.Subtypeに定義があるが、他のライブラリからimportされていると思われる。

-- 型変数と必要な型クラスの宣言 この宣言は必要。もともとUだったのをαに変えた。
variable {α : Type} [DecidableEq α] [Fintype α][Nonempty α]

--包含関係で極大で定義しているが、サイズ最大のほうがいいかも。
--なくす方向もあるかもしれないが、現状では利用している。
def is_maximal_hyperedge (i : IdealFamily α) (H : Finset α): Prop :=
  i.sets H = true ∧ H ≠ i.ground ∧ (∀ (A: Finset α), (i.sets A → H ⊂ A → A = i.ground))

omit [DecidableEq α] [Fintype α] [Nonempty α] in
lemma max_card_eq_sup  (elements : Finset (Finset α)) (H : Finset α) (H_mem : H ∈ elements) (H_max : (∀ s, s ∈ elements → s.card ≤ H.card)) :
  H.card = elements.sup (λ s => s.card) :=
  by
    apply le_antisymm
    · apply Finset.le_sup
      simp_all only
    · simp_all only [Finset.sup_le_iff, implies_true]

-- Ideal集合族に対する極大ハイパーエッジの存在定理
omit [Nonempty α] in
theorem exists_maximal_hyperedge (sf : IdealFamily α) :
  ∃ H : Finset α, H ≠ sf.ground ∧ sf.sets H ∧ ∀ ⦃A : Finset α⦄, sf.sets A → H ⊆ A → (A = H ∨ A = sf.ground) :=
by
  -- イデアル集合族の要素をフィルタリング
  let elements := Finset.filter (λ s => sf.sets s = true && s ≠ sf.ground) (Finset.powerset Finset.univ)
  -- 空でないことを証明
  have hne : elements.Nonempty :=
    by
      use ∅
      rw [Finset.mem_filter]
      constructor
      simp [sf.has_empty]
      simp [elements, elements, Finset.filter_eq']
      constructor
      exact sf.has_empty
      exact sf.nonempty_ground.ne_empty.symm

  rw [Finset.nonempty_iff_ne_empty] at hne
  -- 最大の要素を選ぶ
  obtain ⟨H, H_mem, H_max⟩ := exists_max_card elements hne
  use H
  have H_mem_elements : H ∈ elements := H_mem
  have H_mem_def : H ∈ Finset.filter (λ s => sf.sets s = true && s ≠ sf.ground) (Finset.powerset Finset.univ) := H_mem_elements
  have H_mem_filter : sf.sets H ∧ H ≠ sf.ground :=
    by simp [Finset.mem_filter] at H_mem_def; exact H_mem_def
  constructor
  exact H_mem_filter.2  -- H ≠ Finset.univを示している。
  constructor
  exact H_mem_filter.1
  -- 極大性を証明
  intros A hA hHA
  by_cases hAeq : A = sf.ground
  simp [hAeq]
  have hAne : A ≠ sf.ground :=
  by
    intro h_contra
    rw [h_contra] at hAeq
    contradiction
  have A_mem_elements : A ∈ elements :=
  by
    rw [Finset.mem_filter]
    constructor
    case left => simp
    simp [hA, hAne]

  by_cases hAeqH : A = H
  exact Or.inl hAeqH
  have hH_ssubset_A : H ⊂ A :=
    by
      rw [Finset.ssubset_iff_subset_ne]
      constructor
      exact hHA
      simp [hAeqH, hAne]
      contrapose! hAeqH
      exact hAeqH.symm

  have h_card_lt : Finset.card H < Finset.card A :=
    by
      exact Finset.card_lt_card hH_ssubset_A

  have H_max2 :(H_max : H.card = elements.sup (λ s => s.card)) → ∀ s ∈ elements, s.card ≤ H.card :=
  by
    intro hmax
    --rename_i inst inst_1 _
    intro s a
    simp_all only [ne_eq, decide_not, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, not_false_eq_true, and_self, true_and, elements]
    obtain ⟨left_1, right_1⟩ := a
    apply Finset.le_sup
    simp_all only [Finset.mem_filter, Finset.mem_univ, not_false_eq_true, and_self]

  have h_contra : H.card < H.card :=
    by
      rw [max_card_eq_sup elements H H_mem (H_max2 H_max)] at h_card_lt
      have h_le_sup : A.card ≤ elements.sup (λ s => s.card) := Finset.le_sup A_mem_elements
      rw [max_card_eq_sup]
      linarith
      omega
      linarith
  omega

-- Hからxを除いたハイパーエッジを生成する関数
def map_hyperedge (sf : IdealFamily α) (x : α) (G: Finset α)(H : Finset α) : Finset α :=
  if H = sf.ground then G
  else Finset.erase H x

-- x notin Gのときにmap_hyperedgeで移った先がhyperedgeであることの定理
-- Gが極大である条件の代わりに、少し弱いGがhyperedgeである条件を引数にした。
omit [Nonempty α] in
theorem map_hyperedge_is_hyperedge (sf : IdealFamily α) (x : α) (G : Finset α) (gsets : sf.sets G) (H : Finset α) :
  (sf.sets H) → x ∉ G → (sf.sets (map_hyperedge sf x G H)) :=
by
  -- 仮定を導入
  intros hH _
  -- map_hyperedgeの定義を展開
  unfold map_hyperedge
  -- H が全体集合である場合とそうでない場合を考える
  by_cases h_univ : H = sf.ground
  -- H が全体集合である場合
  case pos =>
    -- 全体集合に対する処理
    rw [h_univ]
    --simp [hH]
    -- 極大ハイパーエッジの性質を利用
    simp
    exact gsets
  -- H が全体集合でない場合
  case neg =>
    -- 部分集合の性質を利用 h_subsetとhH'は使ってないように見えて、ないとエラーになる。
    have h_subset : (Finset.erase H x) ⊆ H := Finset.erase_subset x H
    have hH' : sf.sets (Finset.erase H x):=
      by
        --let HX := (Finset.erase H x)
        exact sf.down_closed (H.erase x) H hH h_univ h_subset
        ---(down_closed : ∀ {A B : Finset α}, sets B → A ⊆ B → sets A)
    have hH'' : sf.sets (Finset.erase H x)  :=
      by
        simp_all only
    rw [if_neg h_univ]
    exact hH''

omit [Nonempty α] in
lemma G_union_x_hyperedge_or_univ (sf : IdealFamily α) (x : α) (G : Finset α) (imh : is_maximal_hyperedge sf G) :
  x ∉ G → ¬sf.sets (G ∪ {x}) ∨ G ∪ {x} = sf.ground :=
  by
    intro hxG  -- x ∉ G を仮定
    -- G ∪ {x} がハイパーエッジである場合を考える
    by_cases h : sf.sets (G ∪ {x})
    -- G ∪ {x} がハイパーエッジである場合
    · right
      -- G が極大ハイパーエッジであることを利用
      have G_max := imh.right.2
      specialize G_max (G ∪ {x}) h
      -- G ⊂ G ∪ {x} であることを示す
      have G_subset : G ⊂ G ∪ {x} :=
        by
          apply ssubset_insert
          exact hxG
      -- G ∪ {x} が全体集合であることを示す
      simp_all only [true_implies]
      --exact G_max G_subset
    -- G ∪ {x} がハイパーエッジでない場合
    · left
      exact h

-- H1が全体集合の場合の矛盾を示す補助定理
omit [Nonempty α] in
lemma map_hyperedge_univ_eq (sf : IdealFamily α) (x : α) (G : Finset α) (imh : is_maximal_hyperedge sf G) (H : Finset α) :
  x ∈ H → sf.sets H → x ∉ G → H ≠ sf.ground → map_hyperedge sf x G H ≠ G :=
  by
    -- 仮定を導入
    intro hxH  -- x ∈ Hであることを仮定
    intro hsxH  -- Hがハイパーエッジであることを仮定
    intro hxG  -- x ∉ Gであることを仮定
    intro hH   -- Hが全体集合でないことを仮定
    -- map_hyperedgeの定義を展開
    unfold map_hyperedge
    -- H が全体集合である場合とそうでない場合を考える
    by_cases h : H = sf.ground
    -- H が全体集合である場合
    · simp [h]
      -- H が全体集合であることと矛盾
      contradiction -- Hが全体集合である場合、仮定に矛盾
    -- H が全体集合でない場合
    · simp [h]  -- Hが全体集合でない場合
      -- H から x を取り除いた結果が G であると仮定
      intro h_eq
      -- H = G ∪ {x} であることを示す
      have H_eq : H = G ∪ {x} := erase_insert_eq H G x hxH h_eq
      -- G ∪ {x} がハイパーエッジでないか全体集合であることを示す
      have H_hyperedge_or_univ := G_union_x_hyperedge_or_univ sf x G imh hxG --imhを本質的に利用。
      -- ¬sf.sets (G ∪ {x}) = true ∨ G ∪ {x} = sf.ground
      match H_hyperedge_or_univ with
      | Or.inl h_not_hyperedge =>
        -- H = G ∪ {x} がハイパーエッジでない場合の処理
        -- Hはhyperedgeであることと矛盾
        rw [←H_eq] at h_not_hyperedge
        contradiction
      | Or.inr h_univ =>
        --exact hxG h_univ
        -- H = G ∪ {x} が全体集合の場合の処理
        rw [←H_eq] at h_univ
        contradiction

-- 非全体集合同士の結果が等しい場合の条件を示す補助定理
omit [Nonempty α] in
lemma map_hyperedge_nonuniv_eq (sf : IdealFamily α) (x : α) (G : Finset α) (H1 H2 : Finset α) :
x ∈ H1→ x ∈ H2 → x ∉ G → H1 ≠ sf.ground → H2 ≠ sf.ground → map_hyperedge sf x G H1 = map_hyperedge sf x G H2 → Finset.erase H1 x = Finset.erase H2 x :=
  by
    -- 仮定を導入
    intro _ _ _ hH1 hH2 h_map
    -- map_hyperedgeの定義を展開し、H1とH2が全体集合でない場合の処理を行う
    unfold map_hyperedge at h_map
    rw [if_neg hH1, if_neg hH2] at h_map
    -- 結果が等しいことからFinset.erase H1 x = Finset.erase H2 xであることを結論づける
    exact h_map

-- サブタイプの等式を証明する補助定理
omit [Nonempty α] in
theorem subtype_eq_of_val_eq (sf : IdealFamily α) (x : α) (H1 H2 : { H // sf.sets H ∧ x ∈ H }) :
  H1.1 = H2.1 → H1 = H2 :=
  by
   intro a
   obtain ⟨val, property⟩ := H1
   obtain ⟨val_1, property_1⟩ := H2
   obtain ⟨left, right⟩ := property
   obtain ⟨left_1, right_1⟩ := property_1
   simp_all only



-- map_hyperedge の単射性を証明する補題
--map_hyperedge_univ_eqを呼ぶ時にimhを本質的に利用している。
omit [Nonempty α] in
lemma map_hyperedge_injective (sf : IdealFamily α) (x : α) (G: Finset α) (imh : is_maximal_hyperedge sf G)  :
  x ∉ G → Function.Injective (λ H : {H // sf.sets H  ∧ x ∈ H} => map_hyperedge sf x G H.1):=
  by
    intro hxG  -- x ∉ Gであることを仮定
    -- 単射性の証明
    intros H1 H2 h_map  -- 任意のH1, H2に対して、map_hyperedgeの結果が等しいことを仮定
    -- H1, H2 : { H // sf.sets H ∧ x ∈ H }
    -- h_map : (fun H => map_hyperedge sf x G imh ↑H) H1 = (fun H => map_hyperedge sf x G imh ↑H) H2
    -- map_hyperedge_nonuniv_eqを利用して、Finset.erase H1.1 x = Finset.erase H2.1 xであることを示す
    contrapose! h_map
    have hmap1: H1.1 ≠ H2.1 := by
       --subtype_eq_of_val_eqを使う
       -- H1.1 = H2.1を仮定して矛盾を導く
       -- h_mapはH1 ≠ H2である
        intro h_contra
        have hh122: H1 = H2 := by
          exact Subtype.ext h_contra
        contradiction
    -- 移った先が違うことを示す
    by_cases h_univ1 : H1.1 = sf.ground
    -- H1.1 = Finset.univ の場合
    have h_univ2 : H2.1 ≠ sf.ground :=
      by
          simp_all only [ne_eq]
          obtain ⟨val, property⟩ := H1
          obtain ⟨val_1, property_1⟩ := H2
          obtain ⟨left, right⟩ := property
          obtain ⟨left_1, right_1⟩ := property_1
          simp_all only [Subtype.mk.injEq, not_false_eq_true]
          subst h_univ1
          --simp_all only [Finset.mem_univ]
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [Finset.mem_univ, not_true_eq_false]

    have value1:map_hyperedge sf x G H1.1 = G := by
      simp [map_hyperedge, h_univ1]
    rw [value1]
    --rw [decide_eq_true_eq] at H2
    exact (map_hyperedge_univ_eq sf x G imh H2.1 H2.2.2 H2.2.1 hxG h_univ2).symm
    by_cases h_univ2: H2.1 = sf.ground
    have value2:map_hyperedge sf x G H2.1 = G := by
      simp [map_hyperedge, h_univ2]
    rw [value2]
    exact map_hyperedge_univ_eq sf x G imh H1.1 H1.2.2 H1.2.1 hxG h_univ1
    -- H1.1 ≠ Finset.univ かつ H2.1 ≠ Finset.univ の場合
    contrapose! h_map
    have result: H1.1.erase x = H2.1.erase x := ((map_hyperedge_nonuniv_eq sf x G H1.1 H2.1) H1.2.2 H2.2.2 hxG h_univ1 h_univ2) h_map
    -- H1.1.erase x = H2.1.erase x から H1.1 = H2.1 であることを示す
    have h_erase_eq : H1.1 = H2.1 :=
      by
        exact (erase_inj_of_mem  H1.2.2 H2.2.2).mp result
    exact subtype_eq_of_val_eq sf x H1 H2 h_erase_eq

omit [Nonempty α] in
lemma card_filter_add_card_filter_compl (sf : IdealFamily α) (v : α) [DecidablePred sf.sets]  :
  (Finset.filter (λ H=> sf.sets H ∧ v ∈ H) (sf.ground.powerset)).card +
  (Finset.filter (λ H=> sf.sets H ∧ v ∉ H) (sf.ground.powerset)).card =
  (Finset.filter (λ H=> sf.sets H) (sf.ground.powerset)).card :=
  by
    let with_v := Finset.filter (λ H=> sf.sets H ∧ v ∈ H) (sf.ground.powerset)
    have wv:with_v = Finset.filter (λ H=> sf.sets H ∧ v ∈ H) (sf.ground.powerset) := rfl
    let without_v := Finset.filter (λ H=> sf.sets H ∧ v ∉ H) (sf.ground.powerset)
    have wov:without_v = Finset.filter (λ H=> sf.sets H ∧ v ∉ H) (sf.ground.powerset) := rfl
    let all := Finset.filter (λ H=> sf.sets H) (sf.ground.powerset)
    have w:all = Finset.filter (λ H=> sf.sets H) (sf.ground.powerset) := rfl

    -- `with_v` と `without_v` は交わらない
    have h_disjoint : Disjoint with_v without_v :=
      by
        simp_all only [with_v, without_v, all]
        rw [Finset.disjoint_left]
        intro a a_1
        simp_all only [Finset.mem_filter, Finset.mem_univ, true_and, not_true_eq_false, and_false, not_false_eq_true]

    -- `with_v ∪ without_v = all`
    have h_union : with_v ∪ without_v = all :=
      by
        ext H
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        constructor
        · intro h --with_v ∪ without_v = allの左から右
          cases h with
          |inl hl =>
           --obtain ⟨h_sets, h_v⟩ := h --with_vのほう。
           rw [wv] at hl
           simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hl
           exact Finset.mem_filter.mpr ⟨hl.1, hl.2.1⟩
          |inr hr =>
           simp [all, Finset.mem_filter.mp hr]
           -- goal H ∈ with_v ∨ H ∈ without_v
        --- --with_v ∪ without_v = allの右から左
        · rw [w]
          intro h
          rw [wv,wov]
          by_cases hh: v ∈ H
          · simp_all only [Finset.mem_filter, Finset.mem_univ, true_and, and_self, not_true_eq_false, and_false,
            or_false, with_v, without_v, all]
          · simp_all only [Finset.mem_filter, Finset.mem_univ, true_and, and_self, not_true_eq_false, and_false,
            or_false, with_v, without_v, all]
            tauto

    -- `with_v` と `without_v` のカードの合計が `all` のカードに等しいことを証明
    rw [wv, wov, w] at h_union
    rw [←h_union]
    rw [←wv, ←wov]
    rw [Finset.card_union_of_disjoint h_disjoint]

-- hyperedges_without_v の位数は family_size_sf - degree_v であることを示す補題
omit [Nonempty α] in
lemma card_hyperedges_without_v (sf : IdealFamily α) (v : α) [DecidablePred sf.sets]:
  Finset.card ((sf.ground.powerset).filter (λ H => sf.sets H ∧ v ∉ H)) =
  ideal_family_size sf - ideal_degree sf v :=
  by
    let with_v := Finset.filter (λ H => sf.sets H ∧ v ∈ H) (sf.ground.powerset)
    have wv:with_v = Finset.filter (λ H=> sf.sets H ∧ v ∈ H) (sf.ground.powerset) := rfl
    let without_v := Finset.filter (λ H => sf.sets H ∧ v ∉ H) (sf.ground.powerset)
    let all := Finset.filter (λ H => sf.sets H) (sf.ground.powerset)

    have h_card_add : with_v.card + without_v.card = all.card :=
      by exact card_filter_add_card_filter_compl sf v

    have h_card_with : with_v.card = ideal_degree sf v :=
    by
      rw [ideal_degree]
      rw [wv]
      rw [degree]
      simp_all only [Finset.powerset_univ, with_v, without_v, all]
      --rw [Finset.filter_congr_decidable]
      simp [decide_eq_true_eq]

    have h_card_all : all.card = ideal_family_size sf :=
    by
      rw [ideal_family_size, number_of_hyperedges]
      simp [all]
      congr
    rw [h_card_with, h_card_all] at h_card_add
    simp_all only [with_v, without_v, all]
    simp_all only [ideal_family_size,ideal_degree]
    simp_all only [number_of_hyperedges,degree]
    simp [h_card_with, h_card_all]
    omega

-- hyperedges_with_v の位数は degree_v であることを示す補題
omit [Nonempty α]
lemma card_hyperedges_with_v (sf : IdealFamily α) (v : α) :
  Finset.card ((sf.ground.powerset).filter (λ H => sf.sets H ∧ v ∈ H)) = ideal_degree sf v :=
  by
    rw [ideal_degree]
    rw [degree]
    --rw [Finset.powerset_univ]
    --rw [all_subsets]
    rw [Finset.filter_congr_decidable]
    --dsimp [hyperedges_with_v]
    simp [decide_eq_true_eq]

--ここのFinset.univをsf.groundに変える必要あり。
omit [Fintype α] in
lemma exists_element_not_in_univ (H : Finset α)(U: Finset α):(H ⊆ U) → (H ≠ U) → ∃ x ∈ U, x ∉ H :=
  by
    -- H が全体集合でないことから、U と H の差集合が空でないことを示す
    intro h hne

    -- 真部分集合の定義から、H ⊆ U かつ H ≠ U を得る
    --obtain ⟨_, hneq⟩ := Finset.ssubset_iff_subset_ne.mp h
    -- 対偶法を使用して証明する
    by_contra h'
    -- h' を反転させる
    push_neg at h'
    have h_forall : ∀ x : α, x ∈ U → x ∈ H :=
    by
      intro x
      specialize h' x
      exact h'

    have h_subset : U ⊆ H := by
      intro x hx
      exact h_forall x hx

    -- h' が成り立つと仮定すると、H = U となる
    have h_eq : H = U := by
      exact Finset.Subset.antisymm h h_subset

    -- これは H ≠ U という仮定に反する
    contradiction

--
omit [Fintype α] in
lemma strict_subset_implies_univ (H A U: Finset α):
  ((H ⊂ A → A = U) ↔ (H ⊆ A → A = H ∨ A = U)) :=
  by
    --intro _ --H_sub_A A_sub_U
    constructor
    intros h H_sub_A
    by_cases h_eq : A = H
    -- A = H の場合
    · left
      exact h_eq
    -- A ≠ H の場合
    · right
      have h_ssub : H ⊂ A :=
        by
          rw [Finset.ssubset_iff_subset_ne]
          have hna:H ≠ A := by
            intro h_contra
            rw [h_contra] at h_eq
            contradiction
          exact ⟨H_sub_A, hna⟩
      exact h h_ssub
      --逆側
    intros h H_ssub_A
    --H_ssub_A : H ⊂ A
    --goal : A = Finset.univ
    have H_sub_A : H ⊆ A :=
    by
      exact H_ssub_A.subset
    have aor: A = H ∨ A = U:=
    by
      exact h H_sub_A
    cases aor with
    | inl h_eq => -- A = H の場合
      exfalso
      have h_eq_symm := h_eq.symm
      rw [h_eq_symm] at H_ssub_A
      exact ssubset_irrefl A H_ssub_A
    | inr h_eq => exact h_eq

lemma map_hyperedge_excludes_x (sf : IdealFamily α) (x : α) (G : Finset α)  (H : Finset α) :
  sf.sets H → x ∉ G → x ∈ H → x ∉ map_hyperedge sf x G H :=
  by
    intros _ hxG _
    -- `H = Finset.univ` の場合と `H ≠ Finset.univ` の場合に分けて考えます
    by_cases H_eq_univ : H = sf.ground
    -- `H = Finset.univ` の場合
    · rw [H_eq_univ, map_hyperedge]
      -- この場合、`map_hyperedge sf x G imh H = G` です
      -- 仮定から `x ∉ G` であるため、`x ∉ map_hyperedge sf x G imh H` となります
      simp [hxG]
    -- `H ≠ Finset.univ` の場合
    · rw [map_hyperedge]
      -- この場合、`map_hyperedge sf x G imh H = Finset.erase H x` です
      -- `Finset.erase` の性質から、`x ∉ Finset.erase H x` であることは明らかです
      -- したがって、`x ∉ map_hyperedge sf x G imh H` です
      simp [H_eq_univ]



-- Ideal Version of Frankl's Conjecture の証明
theorem ideal_version_of_frankl_conjecture :
  --∀ (U : Type) [DecidableEq U] [Fintype U] [Nonempty U],
  ∀ (sf : IdealFamily α),
    ∃ (v : α), v ∈ sf.ground ∧ 2 * ideal_degree sf v ≤ ideal_family_size sf :=
  by
    -- 型変数と必要な型クラスの宣言
    intros sf

    -- 最大ハイパーエッジ G の存在を示す
    obtain ⟨G, G_ne_univ, G_in_sf, G_max⟩ := exists_maximal_hyperedge sf

    -- G に属さない要素 v の存在を示す
    -- lemma exists_element_not_in_univ (H : Finset α)(U: Finset α):(H ⊆ U) → (H ≠ U) → ∃ x ∈ U, x ∉ H
    obtain ⟨v, _, v_not_in_G⟩ := exists_element_not_in_univ G sf.ground (sf.inc_ground G G_in_sf) G_ne_univ

    -- G の極大性を証明
    have G_maximal : is_maximal_hyperedge sf G :=
      by
        constructor
        · simp [decide_eq_true_eq]
          exact G_in_sf
        constructor
        · exact G_ne_univ
        · intro A hA --H_sub_A
          --lemma strict_subset_implies_univ (H A U: Finset α): (H ⊆ U) → (A ⊆ U)→
          --((H ⊂ A → A = U) ↔ (H ⊆ A → A = H ∨ A = U))

          apply (strict_subset_implies_univ G A sf.ground ).mpr
          exact G_max hA

    -- hyperedges_with_v と hyperedges_without_v を定義
    let hyperedges_with_v := ((sf.ground.powerset)).filter (λ H => sf.sets H ∧ v ∈ H)
    let hyperedges_without_v := ((sf.ground.powerset)).filter (λ H => sf.sets H ∧ v ∉ H)

    -- 写像の単射性を示す
    have map_injective : Function.Injective (λ H : {H // sf.sets H ∧ v ∈ H}=> map_hyperedge sf v G H.1) :=
      map_hyperedge_injective sf v G G_maximal v_not_in_G

    -- 写真の値域が sf.sets に含まれることを示す
    have map_is_hyperedge : ∀ H, H ∈ hyperedges_with_v → (map_hyperedge sf v G H) ∈ hyperedges_without_v :=
      by
        intros H hH
        simp only [Finset.mem_filter] at hH
        dsimp [hyperedges_with_v, hyperedges_without_v] at hH
        simp only [Finset.mem_filter] at hH
        simp [hyperedges_without_v]
        have h1 : sf.sets (map_hyperedge sf v G  H)  :=
          map_hyperedge_is_hyperedge sf v G G_in_sf H hH.2.1 v_not_in_G
        have h2 : v ∉ (map_hyperedge sf v G  H) :=
          map_hyperedge_excludes_x sf v G  H hH.2.1 v_not_in_G hH.2.2
        --        rw [Finset.mem_powerset]
        constructor
        --have h1' : sf.sets (map_hyperedge sf v G H) := by
        --  rw [h1]
        exact sf.inc_ground (map_hyperedge sf v G H) h1
        exact ⟨h1, h2⟩

    -- 写像の定義域と終域を設定する
    let domain := { H : Finset α // sf.sets H ∧ v ∈ H }
    let codomain := { H : Finset α // sf.sets H ∧ v ∉ H }

    -- 写像の定義
    let f : domain → codomain :=
      λ HH =>
    let mapped_H := map_hyperedge sf v G HH.1
    have h1 : sf.sets mapped_H := map_hyperedge_is_hyperedge sf v G G_in_sf HH.1 HH.2.1 v_not_in_G
    have h2 : v ∉ mapped_H := map_hyperedge_excludes_x sf v G  HH.1 HH.2.1 v_not_in_G HH.2.2
    ⟨mapped_H, ⟨h1, h2⟩⟩

    -- 写像が単射であることを示す
    have f_injective : Function.Injective f :=
      by
        intros a b h
        apply map_injective
        have eq_mapped_H : map_hyperedge sf v G  a.1 = map_hyperedge sf v G b.1 := by
          apply congr_arg Subtype.val h
        exact eq_mapped_H

    -- 定義域と終域の大きさが等しいことを示す
    have h_inj_card :  (Finset.univ : Finset domain).card ≤ (Finset.univ : Finset codomain).card :=
      Fintype.card_le_of_injective f f_injective

    -- hyperedges_without_v の位数は family_size_sf - degree_v であることを使う
    have h_size_without_v : hyperedges_without_v.card = ideal_family_size sf - ideal_degree sf v :=
      card_hyperedges_without_v sf v

    -- hyperedges_with_v の位数は degree_v であることを使う
    have h_size_with_v : hyperedges_with_v.card = ideal_degree sf v :=
      card_hyperedges_with_v sf v

    -- hyperedges_with_v と hyperedges_without_v の大きさの和が family_size_sf であることを使う
    have h_family_size : hyperedges_with_v.card + hyperedges_without_v.card = ideal_family_size sf :=
      by
        rw [card_filter_add_card_filter_compl sf v]
        simp_all only [ne_eq, Finset.mem_univ, Finset.mem_filter, true_and, and_imp, Finset.card_univ,
          hyperedges_with_v, hyperedges_without_v, domain, codomain, f]
        rw [ideal_family_size]
        congr

    -- (Finset.univ : Finset domain).card が hyperedges_with_v.card に等しいことを示す
    have h_domain_card : (Finset.univ : Finset domain).card = hyperedges_with_v.card :=
    by
      simp only [domain, ideal_degree, Finset.univ, Finset.filter]
      apply Fintype.card_of_subtype
      intro x -- xはdomainの要素という条件は？
      simp [hyperedges_with_v]
      intro sfx _
      --rw [all_subsets]
      --rw [Finset.mem_powerset]
      exact sf.inc_ground x sfx

    -- (Finset.univ : Finset codomain).card が hyperedges_without_v.card に等しいことを示す
    have h_codomain_card : (Finset.univ : Finset codomain).card = hyperedges_without_v.card :=
    by
      simp only [codomain, ideal_degree, Finset.univ, Finset.filter]
      apply Fintype.card_of_subtype
      intro x
      simp [hyperedges_without_v]
      intro sfx _
      --rw [all_subsets]
      --rw [Finset.mem_powerset]
      exact sf.inc_ground x sfx

    -- hyperedges_without_v.card ≥ hyperedges_with_v.card を示す
    have _ : hyperedges_without_v.card ≥ hyperedges_with_v.card :=
      by
        rw [←h_domain_card, ←h_codomain_card]
        assumption

    -- 2 * ideal_degree sf v ≤ ideal_family_size sf を示す
    have h_degree_le_size : 2 * ideal_degree sf v ≤ ideal_family_size sf :=
      by
        rw [← h_size_with_v]
        rw [← h_family_size]
        linarith

    -- 結論を得る
    simp_all only [ne_eq, Finset.mem_filter, and_imp, Finset.card_univ, ge_iff_le, hyperedges_with_v,
      hyperedges_without_v, domain, codomain, f]
    use v

--以下は、AverageRare.leanに移動したので、消して良い。
---------------------------------------
--variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {α : Type*} [DecidableEq α]


omit [DecidableEq α] in
lemma decarte (A : Finset α) (B : Finset (Finset α)) (a : α) (b : Finset α)
  (ha : a ∈ A) (hb : b ∈ B) : (a, b) ∈ A.product B := by
  -- `Finset.product` の定義に基づき、`(a, b)` は `A.product B` に属する
  apply Finset.mem_product.2 ⟨ha, hb⟩

-- 定義: FG.product filtered_powerset は filtered_powerset のデカルト積
def FG_product (FG :Finset α) (filtered_powerset : Finset (Finset α))[DecidableEq filtered_powerset] : Finset (α × Finset α) :=
  FG.product filtered_powerset

-- 定義: filtered_product は FG.product filtered_powerset の中で p.1 ∈ p.2 を満たすペアの集合
def filtered_product (FG :Finset α) (filtered_powerset : Finset (Finset α)) [DecidableEq filtered_powerset]: Finset (α × Finset α)   :=
  (FG_product FG filtered_powerset).filter (λ p => (p.1 ∈ p.2))

-- 補題: x ⊆ FG であれば, FG.filter (λ a, a ∈ x ) = x
lemma filter_eq_self_of_subset (FG : Finset α) (x : Finset α)
  (h_subset : x ⊆ FG) :
  FG.filter (λ a => a ∈ x ) = x := by
  ext a
  constructor
  intro ha
  rw [Finset.mem_filter] at ha
  exact ha.right

  intro ha
  rw [Finset.mem_filter]
  constructor
  exact h_subset ha
  simp_all only

-- 主な補題: 任意の x ∈ filtered_powerset に対して、
-- フィルタリング後のカード数は x.card に等しい
lemma filter_card_eq_x_card (FG :Finset α) (filtered_powerset : Finset (Finset α))
  (x : Finset α) (hx : x ∈ filtered_powerset)(hFG: ∀ s:Finset α, s ∈ filtered_powerset → s ⊆ FG) :
  ((filtered_product FG filtered_powerset).filter (λ ab => ab.2 = x)).card = x.card :=
  by
    -- フィルタリング後の集合 S は { (a, x) | a ∈ x }
    let range := (filtered_product FG filtered_powerset).filter (λ ab => ab.2 = x )

    -- 対応する集合 T は { a | a ∈ x }
    let domain := FG.filter (λ a => a ∈ x )

    -- 補題の適用: x ⊆ FG
    have h_subset : x ⊆ FG := by
      simp_all only

    -- 補題を使って domain = x
    have h_domain_eq : domain = x := filter_eq_self_of_subset FG x h_subset

    -- マッピング関数 f : domain → range を定義
    let i: (a:α) → (a ∈ domain) → (α × Finset α) := fun a _ => (a, x)

    have hi: ∀ (a: α) (ha:a ∈ domain), i a ha ∈ range :=
      by
        intros a ha
        simp_all only [Finset.mem_filter, and_true, i, domain, range]
        simp_all only [Finset.mem_filter, domain]
        dsimp [filtered_product]
        dsimp [FG_product]
        simp_all only [Finset.mem_filter, and_true]
        have h1: a ∈ FG := by
          apply hFG
          on_goal 2 => {exact ha
          }
          · simp_all only
        --#check decarte FG filtered_powerset a x h1 hx
        exact decarte FG filtered_powerset a x h1 hx

    -- 関数 i が単射であることを示す
    have inj : ∀ (a: α) (ha:a ∈ domain) (b: α) (hb: b ∈ domain), ((i a ha) = (i b hb)) → a = b :=
      by
        intro a ha b hb hH
        simp_all only [Prod.mk.injEq, and_true, i, domain]

    have surj : ∀ p ∈ range, ∃ a, ∃ (h : a ∈ domain), i a h = p :=
      by
         dsimp [range]
         dsimp [filtered_product]
         dsimp [FG_product]
         dsimp [domain]
         intro p a
         simp_all only [Finset.mem_filter, and_true, Prod.mk.injEq, implies_true, exists_prop, and_self_left, domain,
           i, range]
         obtain ⟨fst, snd⟩ := p
         obtain ⟨left, right⟩ := a
         obtain ⟨_, right_1⟩ := left
         subst right
         simp_all only [Prod.mk.injEq, and_true, exists_eq_right]

    have bij := Finset.card_bij i hi inj surj
    simp_all only [Finset.mem_filter, and_true, Prod.mk.injEq, implies_true, exists_prop, and_imp, Prod.forall,
      exists_eq_right, domain, i, range]

lemma sum_nonneg_of_nonneg {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℤ) (h : ∀ x ∈ s, 0 ≤ f x) :
  0 ≤ s.sum f := by
  apply Finset.sum_induction
  · intro a b a_1 a_2
    omega
  · simp_all only [le_refl]
  intro x a
  simp_all only

lemma sum_posi_of_posi {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℤ) (nonempty: s ≠ ∅) (h : ∀ x ∈ s, 0 < f x) :
  0 < s.sum f := by
  obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty nonempty
  -- sの非空性からa ∈ s を取得
  have h_pos : 0 < f a := h a ha
  rw [Finset.sum_eq_add_sum_diff_singleton ha]
  --simp_all only [ne_eq, singleton_subset_iff, sum_sdiff_eq_sub, sum_singleton, add_sub_cancel, gt_iff_lt]
  apply add_pos_of_pos_of_nonneg
  · exact h_pos
  · apply sum_nonneg_of_nonneg
    intros x hx
    simp_all only [ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
    obtain ⟨left, _⟩ := hx
    exact (h x left).le

lemma sum_nonpos_exists_nonpos {α : Type} [DecidableEq α] (s : Finset α)(nonempty: s ≠ ∅) (f : α → ℤ) (h : s.sum f ≤ 0) :
  ∃ x ∈ s, f x ≤ 0 := by
  by_contra h1
  -- 仮定を否定して、すべての x に対して f x > 0 であると仮定
  push_neg at h1

  have h_pos : 0 < s.sum f := by
    let sn := sum_posi_of_posi s (λ x => f x) nonempty (by simp_all [h1])
    apply lt_of_le_of_ne
    apply le_trans
    on_goal 2 => {exact sn
    }
    simp_all only [zero_add, Int.reduceLE]
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [le_refl]
    simp [a] at sn
  simp_all only [ne_eq]
  exact not_le_of_lt h_pos h
--variable (A B : Type) (C : Finset (A × B))[DecidableEq A][DecidableEq B] [Fintype A] [Fintype B][DecidableEq C]
--variable (a : A)
--#check C.filter (fun ab => (ab.1 = a))

theorem card_sum_over_fst_eq_card_sum_over_snd {A B : Type} [DecidableEq A][DecidableEq B][Fintype A] [Fintype B] (C : Finset (A × B)) :
  C.card = Finset.univ.sum (fun a => (C.filter (fun ab => (ab.1 = a))).card) ∧
  C.card = Finset.univ.sum (fun b => (C.filter (fun ab => ab.snd = b) : Finset (A × B)).card) := by
     -- 第一の等式: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
  constructor
  · -- 第一の等式の証明: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
    --#check @Finset.card_eq_sum_card_fiberwise
    --#check @Finset.card_eq_sum_card_fiberwise A B (fun ab => ab.fst) C
    --{by
    --  search_proof
    --}
    --#check @Finset.card_eq_sum_card_fiberwise
    apply @Finset.card_eq_sum_card_fiberwise (A × B) A _ (fun ab => ab.fst) C Finset.univ
    intro x _
    simp_all only [Finset.mem_univ]
  · -- 第二の等式の証明: C.card = Σ_{b ∈ B} |C.filter (fun ab => ab.snd = b)|
    apply @Finset.card_eq_sum_card_fiberwise (A × B) B _ (fun ab => ab.snd) C Finset.univ
    intros ab _
    exact Finset.mem_univ ab.snd

theorem card_sum_over_fst_eq_card_sum_over_snd_set {α: Type}{β:Finset σ} [DecidableEq β][Fintype β] (C : Finset (β × (Finset β))) :
  C.card = Finset.univ.sum (fun a => (C.filter (fun ab => (ab.1 = a))).card) ∧
  C.card = Finset.univ.sum (fun b => (C.filter (fun ab => ab.snd = b)).card) := by
     -- 第一の等式: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
  constructor
  · -- 第一の等式の証明: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
    --#check @Finset.card_eq_sum_card_fiberwise
    --#check @Finset.card_eq_sum_card_fiberwise A B (fun ab => ab.fst) C
    --{by
    --  search_proof
    --}
    --#check @Finset.card_eq_sum_card_fiberwise
    apply @Finset.card_eq_sum_card_fiberwise (β × Finset β) β _ (fun ab => ab.fst) C Finset.univ
    intro x _
    simp_all only [Finset.mem_univ]
  · -- 第二の等式の証明: C.card = Σ_{b ∈ B} |C.filter (fun ab => ab.snd = b)|
    apply @Finset.card_eq_sum_card_fiberwise (β × Finset β) (Finset β) _ (fun ab => ab.snd) C Finset.univ
    intros ab _
    exact Finset.mem_univ ab.snd

theorem card_sum_over_fst_eq_card_sum_over_snd_set2 {α: Type u}[DecidableEq α][Fintype α] (C : Finset (α × (Finset α))) :
  C.card = Finset.univ.sum (fun a => (C.filter (fun ab => (ab.1 = a))).card) ∧
  C.card = Finset.univ.sum (fun b => (C.filter (fun ab => ab.snd = b)).card) := by
     -- 第一の等式: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
  constructor
  · -- 第一の等式の証明: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
    --#check @Finset.card_eq_sum_card_fiberwise
    --#check @Finset.card_eq_sum_card_fiberwise A B (fun ab => ab.fst) C
    --{by
    --  search_proof
    --}
    --#check @Finset.card_eq_sum_card_fiberwise
    apply @Finset.card_eq_sum_card_fiberwise (α × Finset α) α _ (fun ab => ab.fst) C Finset.univ
    intro x _
    simp_all only [Finset.mem_univ]
  · -- 第二の等式の証明: C.card = Σ_{b ∈ B} |C.filter (fun ab => ab.snd = b)|
    apply @Finset.card_eq_sum_card_fiberwise (α × Finset α) (Finset α) _ (fun ab => ab.snd) C Finset.univ
    intros ab _
    exact Finset.mem_univ ab.snd

--
theorem sum_cardinality_eq [Fintype α](FG : Finset α) [DecidableEq FG] (filtered_powerset : Finset (Finset α)) [DecidableEq filtered_powerset] (fground: FG = Finset.univ) :
  FG.sum (fun x => (FG.powerset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s)).card) =
  filtered_powerset.sum (fun s => s.card) := by
    have hFG: ∀ s:Finset α, s ∈ filtered_powerset → s ⊆ FG := by
      intros s _
      subst fground
      simp_all only [Finset.subset_univ]

  --lemma filter_card_eq_x_card (FG :Finset α) (filtered_powerset : Finset (Finset α))
  --(x : Finset α) (hx : x ∈ filtered_powerset)(hFG: ∀ s:Finset α, s ∈ filtered_powerset → s ⊆ FG) :
  --((filtered_product FG filtered_powerset).filter (λ ab => ab.2 = x)).card = x.card

    let convert_product_to_pair  (fa : Finset α) (fb : Finset (Finset α)) : Finset (α × Finset α) :=
      fa.product fb |>.map (Function.Embedding.refl (α × Finset α))
    let pairs := (convert_product_to_pair FG filtered_powerset) |>.filter (λ p => (p.1 ∈ p.2 : Prop))
    have inc: pairs ⊆ (FG.product filtered_powerset) := by
      simp_all only [Finset.map_refl, Finset.filter_subset, pairs, convert_product_to_pair]
    --let pairs_in_set := { (a, b) | a ∈ FG ∧ b ∈ filtered_powerset ∧ (a, b) ∈ pairs } : Finset (FG × filtered_powerset)

    --#check (FG × filtered_powerset)
    --#check (FG.product filtered_powerset) : Finset (α × Finset α)
    --have inc2: pairs ⊆ (FG × filtered_powerset) := by --積には変換されてない。
    --#check  @card_sum_over_fst_eq_card_sum_over_snd_set α _ _ _ pairs
    --card_sum_over_fst_eq_card_sum_over_snd_set  pairs : pairs.card = ∑ a : α, (Finset.filter (fun ab => ab.1 = a) pairs).card ∧ pairs.card = ∑ b : Finset α, (Finset.filter (fun ab => ab.2 = b) pairs).card
    --#check @card_sum_over_fst_eq_card_sum_over_snd  (Finset α) ((Finset (α × Finset α))) _ _ _ _ _ pairs_in_set --エラーになるのは、積とproductの違いか。
    --#check @card_sum_over_fst_eq_card_sum_over_snd_set2 α _ _ pairs
    --#check h1

    have h1 := @card_sum_over_fst_eq_card_sum_over_snd_set2 α _ _ pairs
    --#check h1
    have h2 := h1.1
    rw [h1.2] at h2
    --simp_all only [Finset.map_refl, Finset.filter_subset, and_self, pairs, convert_product_to_pair]

    dsimp [pairs] at h2
    simp at h2
    dsimp [convert_product_to_pair] at h2
    simp at h2
    --h2の右辺と、ゴールの左辺が近い形。ただし、Finset alphaと、FGの差がある。証明が完了している。
    have equal:  ∑ x : α, (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card = ∑ x ∈ FG, (Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) FG.powerset).card := by
        apply Finset.sum_congr
        simp_all only [Finset.mem_univ]
        --goal  ∑ x : α, (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card = ∑ x ∈ FG, (Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) FG.powerset).card
        intro x hx

        simp_all only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_self, and_true, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_filter]
        -- x in Finset.univとか、filtered_powerset ⊆ Finset.univは使いそう。
        have equal_card :
          (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (Finset.univ.product filtered_powerset))).card =
          (Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset).card :=
        by
          -- 左辺のフィルタの数を右辺のフィルタの数と一致させるため、card_bij を使って両者の対応を構築します

          -- 対応関数を定義します
          let i := (λ s (hs : s ∈ Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset) => (x, s))

          -- 関数 `i` が右辺の要素を左辺に写像することを確認します
          have hi : ∀ (s : Finset α) (hs : s ∈ Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset),
            i s hs ∈ Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (Finset.univ.product filtered_powerset)) := by
            intros s hs
            simp only [i, Finset.mem_filter, and_true, eq_self_iff_true, Prod.fst]
            subst fground
            simp_all only [Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.map_refl,
              Finset.filter_subset, and_self, and_true, pairs, convert_product_to_pair]
            obtain ⟨left, right⟩ := hs
            exact Finset.mem_product.mpr ⟨Finset.mem_univ x, left⟩

          -- 関数 `i` が単射であることを確認します
          have i_inj : ∀ (a₁ : Finset α) (ha₁ : a₁ ∈ Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset)
            (a₂ : Finset α) (ha₂ : a₂ ∈ Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset),
            i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ := by
              intros a₁ a₂ ha₁ ha₂ h
              injection h with h1
              --goal (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (Finset.univ.product filtered_powerset))).card =
              -- (Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset).card

          -- 関数 `i` が全射であることを確認します
          have i_surj : ∀ (b : α × Finset α)
            (hb : b ∈ Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (Finset.univ.product filtered_powerset))),
            ∃ a, ∃ (ha : a ∈ Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset), i a ha = b :=
            by
              intro b hb
              subst fground
              simp_all only [Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and, and_self, and_true,
                and_imp, Prod.mk.injEq, implies_true, Finset.map_refl, Finset.filter_subset, exists_prop, i, pairs,
                convert_product_to_pair]
              obtain ⟨fst, snd⟩ := b
              obtain ⟨left, right⟩ := hb
              obtain ⟨left_1, right_1⟩ := left
              apply Finset.mem_product.mp at left_1
              subst right
              simp_all only [Prod.mk.injEq, true_and, exists_eq_right, and_true]

          -- card_bij を適用して左辺と右辺のカードの数が一致することを示します
          exact (Finset.card_bij i hi i_inj i_surj).symm
        exact equal_card

    --goal ∑ x ∈ FG, (Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) FG.powerset).card = ∑ s ∈ filtered_powerset, s.card
    rw [←equal]
    rw [←h2]
    --どっからequal2が出てきた。そもそも成り立つのか？単なる写し間違いかも。修正する必要がありそう。

    have h_zero : ∀ x : Finset α, x ∈ Finset.univ \ filtered_powerset → (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card = 0 :=
      by
        intro x hx
        rw [Finset.card_eq_zero]
        by_contra h_contra
        push_neg at h_contra
        let tmp_set := (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset)))
        have h_nonempty:tmp_set.Nonempty := by
          subst fground
          simp_all only [Finset.map_refl, Finset.filter_subset, Finset.powerset_univ, and_self, ne_eq, pairs,
            convert_product_to_pair]
          rwa [Finset.nonempty_iff_ne_empty]
        obtain ⟨ab, hab⟩ := h_nonempty
        have h_snd : ab.2 = x := by
          subst fground
          simp_all only [Finset.map_refl, Finset.filter_subset, Finset.powerset_univ, and_self, ne_eq,
            Finset.mem_filter, pairs, convert_product_to_pair, tmp_set]
        have hx : x ∈ filtered_powerset := by
          simp_all only [Finset.map_refl, Finset.filter_subset, Finset.powerset_univ, and_self, ne_eq,
            Finset.mem_filter, pairs, convert_product_to_pair]
          simp [tmp_set] at hab
          obtain ⟨hab_left,hab_right⟩ := hab.1
          apply Finset.mem_product.mp at hab_left
          rw [h_snd] at hab_left
          subst h_snd fground
          simp_all only [not_true_eq_false]
        subst h_snd fground
        simp_all only [not_true_eq_false]
        simp_all only [Finset.mem_sdiff, Finset.mem_univ, not_true_eq_false, and_false]

    let filtered_powerset_comp := (Finset.univ : Finset (Finset α)) \ filtered_powerset

    have disjoint_lem: Disjoint filtered_powerset filtered_powerset_comp:= by
      subst fground
      simp_all only [Finset.map_refl, Finset.filter_subset, Finset.powerset_univ, and_self, Finset.card_eq_zero,
        pairs, convert_product_to_pair, filtered_powerset_comp]
      exact disjoint_sdiff_self_right

    have union_lem: (Finset.univ : Finset (Finset α)) = filtered_powerset ∪ filtered_powerset_comp := by
      subst fground
      simp_all only [Finset.map_refl, Finset.filter_subset, Finset.powerset_univ, and_self, Finset.card_eq_zero,
        Finset.union_sdiff_self_eq_union, Finset.right_eq_union, Finset.subset_univ, filtered_powerset_comp, pairs,
        convert_product_to_pair]

    have sum_zero: ∑ x in filtered_powerset_comp, (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card = 0 := by
      apply Finset.sum_eq_zero
      dsimp [filtered_powerset_comp]
      exact h_zero

    have sum_union: ∑ x in (Finset.univ : Finset (Finset α)), (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card
      = ∑ x in filtered_powerset, (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card
      + ∑ x in filtered_powerset_comp, (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card:= by
      rw [←Finset.sum_union disjoint_lem]
      rw [union_lem]

    have equal_lem: ∑ x : Finset α,(Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card = ∑ x in filtered_powerset, (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card := by
      rw [sum_union]
      rw [sum_zero]
      simp

    rw [equal_lem]
    apply Finset.sum_congr
    exact rfl
    intro x hx
    exact filter_card_eq_x_card FG filtered_powerset x hx hFG









end Ideal
