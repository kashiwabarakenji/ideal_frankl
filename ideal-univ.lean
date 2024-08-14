--newideal.leanをrefactoringしたものから台集合を変えたもの。
--全体集合をUを使っていたのをalphaに変えた。これが正しい使い方と思われる。
--このバージョンがIdeal集合族にrare vertexが存在する定理のメインバージョン。

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Mathlib.Init.Function
import LeanCopilot
--import Mathlib.Data.Subtype --Subtypeは使っているが、importしなくても大丈夫かも。
--Mathlib.Data.Subtypeに定義があるが、他のライブラリからimportされていると思われる。

-- 型変数と必要な型クラスの宣言 この宣言は必要。もともとUだったのをαに変えた。
variable {α : Type} [DecidableEq α] [Fintype α][Nonempty α]

-- 空集合と全体集合が異なることの証明
theorem empty_ne_univ : (∅ : Finset α) ≠ Finset.univ :=
  by
    -- 各型クラスのインスタンスを取得
    rename_i _ inst_1 inst_2
    -- 証明を進めるために必要な簡約
    simp_all only [ne_eq]
    -- 矛盾を導く
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp [Finset.eq_univ_iff_forall] at a

-- SetFamily 構造体の定義
structure SetFamily (α : Type) :=
  (ground : Finset α) -- 全体集合
  (sets : (Finset α) → Bool)  -- 集合族を定義する関数
  (inc_ground: sets s → s ⊆ ground) -- 全体集合が含まれる
  (nonempty_ground : ground.Nonempty)

-- 空集合がセットに含まれることを定義
def has_empty (sf : SetFamily α) : Prop :=
  sf.sets ∅

-- 全体集合がセットに含まれることを定義
def has_univ (sf : SetFamily α) : Prop :=
  sf.sets Finset.univ

-- セットが交差に対して閉じていることを定義
def is_closed_under_intersection (sf : SetFamily α) : Prop :=
  ∀ (A B : Finset α), sf.sets A → sf.sets B → sf.sets (A ∩ B)

-- 任意の型 α に対する部分集合の集合を全て列挙する関数
def all_subsets {α : Type} [DecidableEq α] (s : Finset α) : Finset (Finset α) :=
  s.powerset

-- セットの頂点の次数を定義
def degree (sf : SetFamily α) (v : α) : ℕ :=
  Finset.card (Finset.filter (λ s => sf.sets s ∧ v ∈ s) (all_subsets sf.ground))

-- セットのサイズを定義
def family_size (sf : SetFamily α) : ℕ :=
  Finset.card (Finset.filter (λ s => sf.sets s = true) (all_subsets sf.ground))

-- 頂点がレアであることを定義
def is_rare (sf : SetFamily α) (v : α) : Prop :=
  2 * degree sf v ≤ family_size sf

-- Ideal Family の条件を定義
def is_ideal (sf : SetFamily α) : Prop :=
  has_empty sf ∧ has_univ sf ∧
  (∀ (A B : Finset α), sf.sets B → A ⊆ B → sf.sets A)

-- IdealFamily 構造体の定義 [Fintype α] は必要みたい。
structure IdealFamily (α : Type) [DecidableEq α] [Fintype α] extends SetFamily α :=
(empty_mem : sets ∅)  -- 空集合が含まれる
(univ_mem : sets Finset.univ)  -- 全体集合が含まれる
(down_closed : ∀ {A B : Finset α}, sets B → B ≠ ground → A ⊆ B → sets A)  -- ダウンクローズド

-- IdealFamily から SetFamily へのキャスト関数を定義　[DecidableEq α] [Fintype α] は必要。
def to_SetFamily {α : Type} [DecidableEq α] [Fintype α] (sf : IdealFamily α) : SetFamily α :=
    {
      sets := sf.sets,
      ground := sf.ground,
      inc_ground := sf.inc_ground,
      nonempty_ground := sf.nonempty_ground
    }

-- Ideal Family のサイズを計算する関数
def ideal_family_size (sf : IdealFamily α) : ℕ :=
  family_size (to_SetFamily sf)

-- Ideal Family の頂点の次数を計算する関数
def ideal_degree (sf : IdealFamily α) (x : α) : ℕ :=
  degree (to_SetFamily sf) x

--包含関係で極大で定義しているが、サイズ最大のほうがいいかも。
--なくす方向もあるかもしれないが、現状では利用している。
def is_maximal_hyperedge (i : IdealFamily α) (H : Finset α): Prop :=
  i.sets H = true ∧ H ≠ i.ground ∧ (∀ (A: Finset α), (i.sets A → H ⊂ A → A = i.ground))

-- 最大ハイパーエッジの存在を示す補題
lemma card_ne_zero_iff_nonempty (s : Finset α) : s.card ≠ 0 ↔ s ≠ ∅ :=
  by
    constructor
    · intro h
      contrapose! h
      exact Finset.card_eq_zero.mpr h
    · intro h
      contrapose! h
      exact Finset.card_eq_zero.mp h

lemma exists_max_card (S : Finset (Finset α))(h : S ≠ ∅):
  ∃ T ∈ S, T.card = S.sup (λ s => s.card) :=
  by
    -- 空でないことを証明
    rw [←card_ne_zero_iff_nonempty] at h
    rw [Finset.card_ne_zero] at h
    -- 最大の要素が存在することを示す
    have hh := Finset.exists_mem_eq_sup S h (λ s => s.card)
    match hh with
    | ⟨T, hT⟩ =>
      use T
      constructor
      exact hT.left
      exact hT.right.symm

lemma insert_union_eq (G : Finset α) (x : α) : insert x (G ∪ {x}) = G ∪ {x} :=
  by
    simp_all only [Finset.mem_union, Finset.mem_singleton, or_true, Finset.insert_eq_of_mem]

lemma ssubset_insert (G : Finset α) (x : α) : x ∉ G → G ⊂ G ∪ {x} :=
  by

    intro hxG  -- x ∉ G であることを仮定
    -- 部分集合であることを示す
    have subset : G ⊆ G ∪ {x} := by
      intro y hy
      simp_all only [Finset.mem_union, Finset.mem_singleton, true_or]
    -- 真部分集合であることを示す
    have neq : G ≠ G ∪ {x} :=
      by
        intro eq
        -- x ∉ G であるが、x ∈ G ∪ {x} であるため矛盾が生じる
        have x_in_union := Finset.mem_insert_self x G
        rw [eq] at x_in_union
        rw [insert_union_eq] at x_in_union
        rw [eq] at hxG
        contradiction
    -- 部分集合かつ等しくないので真部分集合であることを結論づける
    exact ssubset_iff_subset_ne.mpr ⟨subset, neq⟩

lemma max_card_eq_sup  (elements : Finset (Finset α)) (H : Finset α) (H_mem : H ∈ elements) (H_max : (∀ s, s ∈ elements → s.card ≤ H.card)) :
  H.card = elements.sup (λ s => s.card) :=
  by
    apply le_antisymm
    · apply Finset.le_sup
      simp_all only
    · simp_all only [Finset.sup_le_iff, implies_true]

-- Ideal集合族に対する極大ハイパーエッジの存在定理
theorem exists_maximal_hyperedge (sf : IdealFamily α) :
  ∃ H : Finset α, H ≠ sf.ground ∧ sf.sets H ∧ ∀ ⦃A : Finset α⦄, sf.sets A → H ⊆ A → (A = H ∨ A = sf.ground) :=
by
  -- イデアル集合族の要素をフィルタリング
  let elements := Finset.filter (λ s => sf.sets s && s ≠ sf.ground) (Finset.powerset Finset.univ)
  -- 空でないことを証明
  have hne : elements.Nonempty :=
    by
      use ∅
      rw [Finset.mem_filter]
      constructor
      simp [sf.empty_mem]
      simp [elements, elements, Finset.filter_eq']
      constructor
      exact sf.empty_mem
      exact sf.nonempty_ground.ne_empty.symm

  rw [Finset.nonempty_iff_ne_empty] at hne
  -- 最大の要素を選ぶ
  obtain ⟨H, H_mem, H_max⟩ := exists_max_card elements hne
  use H
  have H_mem_elements : H ∈ elements := H_mem
  have H_mem_def : H ∈ Finset.filter (λ s => sf.sets s && s ≠ sf.ground) (Finset.powerset Finset.univ) := H_mem_elements
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
theorem map_hyperedge_is_hyperedge (sf : IdealFamily α) (x : α) (G : Finset α) (gsets : sf.sets G) (H : Finset α) :
  sf.sets H → x ∉ G → sf.sets (map_hyperedge sf x G H) :=
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
    have hH' : sf.sets (Finset.erase H x) :=
      by
        --let HX := (Finset.erase H x)
        exact sf.down_closed hH h_univ h_subset
        ---(down_closed : ∀ {A B : Finset α}, sets B → A ⊆ B → sets A)
    have hH'' : sf.sets (Finset.erase H x) :=
      by
        simp_all only
    rw [if_neg h_univ]
    exact hH''

lemma erase_insert_eq (H G : Finset α) (x : α) : x ∈ H → Finset.erase H x = G → H = G ∪ {x} :=
  by
    --rename_i inst inst_1 inst_2
    intro a a_1
    subst a_1
    ext1 a_1
    simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, Finset.mem_singleton]
    apply Iff.intro
    · intro a_2
      simp_all only [and_true]
      tauto
    · intro a_2
      cases a_2 with
      | inl h => simp_all only
      | inr h_1 =>
        subst h_1
        simp_all only

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
theorem subtype_eq_of_val_eq (sf : IdealFamily α) (x : α) (H1 H2 : { H // sf.sets H = true ∧ x ∈ H }) :
  H1.1 = H2.1 → H1 = H2 :=
  by
   intro a
   obtain ⟨val, property⟩ := H1
   obtain ⟨val_1, property_1⟩ := H2
   obtain ⟨left, right⟩ := property
   obtain ⟨left_1, right_1⟩ := property_1
   simp_all only

-- フィンセットの消去が等しいことから元のセットが等しいことを証明する補助定理
lemma set_eq_of_erase_eq {A B : Finset α} {x : α} (hxA : x ∈ A) (hxB : x ∈ B) (h : Finset.erase A x = Finset.erase B x) : A = B :=
  by
    apply Finset.ext
    intro y
    constructor
    · intro hy
      by_cases hxy : y = x
      · rw [hxy]
        exact hxB
      · have h1 : y ∈ Finset.erase A x := Finset.mem_erase_of_ne_of_mem hxy hy
        rw [h] at h1
        exact Finset.mem_of_mem_erase h1
    · intro hy
      by_cases hxy : y = x
      · rw [hxy]
        exact hxA
      · have h1 : y ∈ Finset.erase B x := Finset.mem_erase_of_ne_of_mem hxy hy
        rw [←h] at h1
        exact Finset.mem_of_mem_erase h1

-- map_hyperedge の単射性を証明する補題
--map_hyperedge_univ_eqを呼ぶ時にimhを本質的に利用している。
lemma map_hyperedge_injective (sf : IdealFamily α) (x : α) (G: Finset α) (imh : is_maximal_hyperedge sf G)  :
  x ∉ G → Function.Injective (λ H : {H // sf.sets H ∧ x ∈ H} => map_hyperedge sf x G H.1):=
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
        exact set_eq_of_erase_eq  H1.2.2 H2.2.2 result

    exact subtype_eq_of_val_eq sf x H1 H2 h_erase_eq

lemma card_filter_add_card_filter_compl (sf : IdealFamily α) (v : α) :
  (Finset.filter (λ H=> sf.sets H ∧ v ∈ H) (all_subsets sf.ground)).card +
  (Finset.filter (λ H=> sf.sets H ∧ v ∉ H) (all_subsets sf.ground)).card =
  (Finset.filter (λ H=> sf.sets H) (all_subsets sf.ground)).card :=
  by
    let with_v := Finset.filter (λ H=> sf.sets H ∧ v ∈ H) (all_subsets sf.ground)
    have wv:with_v = Finset.filter (λ H=> sf.sets H ∧ v ∈ H) (all_subsets sf.ground) := rfl
    let without_v := Finset.filter (λ H=> sf.sets H ∧ v ∉ H) (all_subsets sf.ground)
    have wov:without_v = Finset.filter (λ H=> sf.sets H ∧ v ∉ H) (all_subsets sf.ground) := rfl
    let all := Finset.filter (λ H=> sf.sets H) (all_subsets sf.ground)
    have w:all = Finset.filter (λ H=> sf.sets H) (all_subsets sf.ground) := rfl

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
           --have hall: H ∈ all_subsets sf.ground := by
           --   simp_all only [Finset.mem_filter, Finset.mem_univ, true_and, and_self, not_true_eq_false, and_false,
           --   or_false, with_v, without_v, all]
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
lemma card_hyperedges_without_v (sf : IdealFamily α) (v : α) :
  Finset.card ((all_subsets sf.ground).filter (λ H => sf.sets H ∧ v ∉ H)) =
  ideal_family_size sf - ideal_degree sf v :=
  by
    let with_v := Finset.filter (λ H => sf.sets H ∧ v ∈ H) (all_subsets sf.ground)
    have wv:with_v = Finset.filter (λ H=> sf.sets H ∧ v ∈ H) (all_subsets sf.ground) := rfl
    let without_v := Finset.filter (λ H => sf.sets H ∧ v ∉ H) (all_subsets sf.ground)
    let all := Finset.filter (λ H => sf.sets H) (all_subsets sf.ground)
    --have w:all = Finset.filter (λ H=> sf.sets H) (all_subsets sf.ground) := rfl

    have h_card_add : with_v.card + without_v.card = all.card :=
      by exact card_filter_add_card_filter_compl sf v

    have h_card_with : with_v.card = ideal_degree sf v :=
    by
      rw [ideal_degree]
      rw [wv]
      rw [degree]
      simp_all only [Finset.powerset_univ, with_v, without_v, all]
      congr

    have h_card_all : all.card = ideal_family_size sf :=
    by
      rw [ideal_family_size, family_size, to_SetFamily]
      --rw [w]
      --simp_all only [Finset.powerset_univ, with_v, without_v, all]
      --congr
    rw [h_card_with, h_card_all] at h_card_add
    simp_all only [with_v, without_v, all]
    simp_all only [ideal_family_size,ideal_degree]
    simp_all only [family_size,degree]
    dsimp [to_SetFamily]
    omega

-- hyperedges_with_v の位数は degree_v であることを示す補題
lemma card_hyperedges_with_v (sf : IdealFamily α) (v : α) :
  Finset.card ((all_subsets sf.ground).filter (λ H => sf.sets H ∧ v ∈ H)) = ideal_degree sf v :=
  by
    rw [ideal_degree]
    rw [degree]
    --rw [Finset.powerset_univ]
    rw [all_subsets]
    rw [Finset.filter_congr_decidable]
    --dsimp [hyperedges_with_v]
    congr


--ここのFinset.univをsf.groundに変える必要あり。
lemma exists_element_not_in_univ (H : Finset α)(U: Finset α):(H ⊆ U) → (H ≠ U) → ∃ x ∈ U, x ∉ H :=
  by
    -- H が全体集合でないことから、U と H の差集合が空でないことを示す
    intro h hne
    --have h_ssub : H ⊂ Finset.univ :=
    --  by
    --    rw [← Finset.ssubset_univ_iff] at h
    --    exact h

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
    ∃ (v : α), 2 * ideal_degree sf v ≤ ideal_family_size sf :=
  by
    -- 型変数と必要な型クラスの宣言
    intros sf

    -- 最大ハイパーエッジ G の存在を示す
    obtain ⟨G, G_ne_univ, G_in_sf, G_max⟩ := exists_maximal_hyperedge sf

    -- G に属さない要素 v の存在を示す
    -- lemma exists_element_not_in_univ (H : Finset α)(U: Finset α):(H ⊆ U) → (H ≠ U) → ∃ x ∈ U, x ∉ H
    obtain ⟨v, _, v_not_in_G⟩ := exists_element_not_in_univ G sf.ground (sf.inc_ground G_in_sf) G_ne_univ

    -- G の極大性を証明
    have G_maximal : is_maximal_hyperedge sf G :=
      by
        constructor
        · exact G_in_sf
        constructor
        · exact G_ne_univ
        · intro A hA --H_sub_A
          --lemma strict_subset_implies_univ (H A U: Finset α): (H ⊆ U) → (A ⊆ U)→
          --((H ⊂ A → A = U) ↔ (H ⊆ A → A = H ∨ A = U))

          apply (strict_subset_implies_univ G A sf.ground ).mpr
          exact G_max hA

    -- hyperedges_with_v と hyperedges_without_v を定義
    let hyperedges_with_v := (all_subsets (sf.ground)).filter (λ H => sf.sets H ∧ v ∈ H)
    let hyperedges_without_v := (all_subsets (sf.ground)).filter (λ H => sf.sets H ∧ v ∉ H)

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
        have h1 : sf.sets (map_hyperedge sf v G  H) = true :=
          map_hyperedge_is_hyperedge sf v G G_in_sf H hH.2.1 v_not_in_G
        have h2 : v ∉ (map_hyperedge sf v G  H) :=
          map_hyperedge_excludes_x sf v G  H hH.2.1 v_not_in_G hH.2.2
        rw [all_subsets]
        rw [Finset.mem_powerset]
        constructor
        exact sf.inc_ground h1
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
      rw [all_subsets]
      rw [Finset.mem_powerset]
      exact sf.inc_ground sfx

    -- (Finset.univ : Finset codomain).card が hyperedges_without_v.card に等しいことを示す
    have h_codomain_card : (Finset.univ : Finset codomain).card = hyperedges_without_v.card :=
    by
      simp only [codomain, ideal_degree, Finset.univ, Finset.filter]
      apply Fintype.card_of_subtype
      intro x
      simp [hyperedges_without_v]
      intro sfx _
      rw [all_subsets]
      rw [Finset.mem_powerset]
      exact sf.inc_ground sfx

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
    exact ⟨v, h_degree_le_size⟩
