import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Mathlib.Init.Function
import LeanCopilot
import Mathlib.Data.Subtype
--import Mathlib.Order.RelClasses --subset.antisymm

variable {U : Type} [DecidableEq U] [Fintype U][Nonempty U]

--空集合と全体集合が異なることの証明
theorem empty_ne_univ : (∅ : Finset U) ≠ Finset.univ :=
  by
    rename_i _ inst_1 inst_2
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp [Finset.eq_univ_iff_forall] at a

structure SetFamily (U : Type) [DecidableEq U] [Fintype U] :=
  (sets : (Finset U) → Bool)
  --(sets_decidable : DecidablePred sets)

def has_empty (sf : SetFamily U) : Prop :=
  sf.sets ∅
--example : has_empty sf → Prop :=

def has_univ (sf : SetFamily U) : Prop :=
  sf.sets Finset.univ

def is_closed_under_intersection (sf : SetFamily U) : Prop :=
  ∀ (A B : Finset U), sf.sets A → sf.sets B → sf.sets (A ∩ B)

def degree (sf : SetFamily U) (v : U) : ℕ :=
  Finset.card (Finset.filter (λ s => sf.sets s ∧ v ∈ s) (Finset.powerset Finset.univ))



-- family_size を定義する関数
def family_size (sf : SetFamily U) : ℕ :=
  Finset.card (Finset.filter (λ s => sf.sets s = true) (Finset.powerset Finset.univ))

def is_rare (sf : SetFamily U) (v : U) : Prop :=
  2 * degree sf v ≤ family_size sf

--rareな頂点の定義is_rareを使った方がいいかもしれない。
theorem frankl_conjecture :
  ∀ (U : Type) [DecidableEq U] [Fintype U] [Nonempty U],
  ∀ (sf : SetFamily U),
    has_empty sf →
    has_univ sf →
    is_closed_under_intersection sf →
    ∃ (v : U), 2 * degree sf v ≤ family_size sf :=
sorry

-- Ideal Family の条件
def is_ideal (sf : SetFamily U) : Prop :=
  has_empty sf ∧ has_univ sf ∧
  (∀ (A B : Finset U), sf.sets B → A ⊆ B → sf.sets A)

structure IdealFamily (U : Type) [DecidableEq U] [Fintype U] extends SetFamily U :=
(empty_mem : sets ∅)
(univ_mem : sets Finset.univ)
(down_closed : ∀ {A B : Finset U}, sets B → A ⊆ B → sets A)

-- Bool を Prop に変換し、DecidablePred インスタンスを提供する
instance decidable_sets (sf : IdealFamily U) : DecidablePred (λ s => sf.sets s = true) :=
  λ s=> decidable_of_iff (sf.sets s = true) (by simp)

-- Ideal Family を構築する関数
--def to_ideal_family (sf : SetFamily U) : SetFamily U :=
--  { sets := λ s => s = ∅ ∨ s = Finset.univ ∨ ∃ (B : Finset U), s ⊆ B ∧ (B = Finset.univ ∨ sf.sets B) }

--包含関係で極大で定義しているが、サイズ最大のほうがいいかも。
def is_maximal_hyperedge (i : IdealFamily U) (H : Finset U): Prop :=
  i.sets H = true ∧ H ≠ Finset.univ ∧ (∀ (A: Finset U), (i.sets A → H ⊂ A → A = Finset.univ))

--極大hyperedgeの存在定理で使う補題
lemma Finset.card_ne_zero_iff_nonempty (s : Finset α) : s.card ≠ 0 ↔ s ≠ ∅ :=
  by
    constructor
    · intro h
      contrapose! h
      exact Finset.card_eq_zero.mpr h
    · intro h
      contrapose! h
      exact Finset.card_eq_zero.mp h

lemma exists_max_card {U : Type} [DecidableEq U] [Fintype U] (S : Finset (Finset U))(h : S ≠ ∅):
  ∃ T ∈ S, T.card = S.sup (λ s => s.card) :=
  by
    rw [←Finset.card_ne_zero_iff_nonempty] at h
    rw [Finset.card_ne_zero] at h
    have hh := Finset.exists_mem_eq_sup S h (λ s => s.card)
    match hh with
    | ⟨T, hT⟩ =>
      use T
      constructor
      exact hT.left
      exact hT.right.symm

--Sがnonemptyである条件は証明には必要ないようだ。あとで消す。
lemma all_elements_le_sup_card {S : Finset (Finset U)} (_ : S.Nonempty) :
  ∀ x ∈ S, x.card ≤ S.sup (λ s => s.card) :=
by
  intros x hx
  apply Finset.le_sup hx

--Ideal集合族には極大なhyperedgeが存在することを示す。位数が最大なものを選んでいる。
--あとに改良版がある。
theorem exists_maximal_hyperedge (sf : IdealFamily U) : ∃ H : Finset U, sf.sets H ∧ ∀ ⦃A : Finset U⦄, sf.sets A → H ⊆ A → (A = H ∨ A = Finset.univ):=
  by
    -- Ideal 集合族の元集合を取得（全体集合を除く）
    let elements := Finset.filter (λ s => sf.sets s && s ≠ Finset.univ) (Finset.powerset Finset.univ)
    -- elements が空でないことを確認
    have hne : elements.Nonempty :=
      by
        use ∅
        rw [Finset.mem_filter]
        constructor
        simp [sf.empty_mem]
        simp [elements, elements, Finset.filter_eq']
        constructor
        exacts [sf.empty_mem,empty_ne_univ]

    rw [Finset.nonempty_iff_ne_empty] at hne
    -- 最大の部分集合を選ぶ
    obtain ⟨H, H_mem, H_max⟩ := exists_max_card elements hne
    -- H が最大ハイパーエッジであることを示す
    use H

    -- H が集合族に属することを示す
    have H_mem_elements : H ∈ elements := H_mem
    have H_mem_def : H ∈ Finset.filter (λ s => sf.sets s && s ≠ Finset.univ) (Finset.powerset Finset.univ) := H_mem_elements
    have H_mem_filter : sf.sets H = true ∧ H ≠ Finset.univ :=
      by simp [Finset.mem_filter] at H_mem_def; exact H_mem_def
    constructor
    exact H_mem_filter.1

    intros A hA hHA
    by_cases hAeq : A = Finset.univ
    -- A が全体集合である場合
    simp [hAeq]
    -- A が全体集合でない場合
    have hAne : A ≠ Finset.univ :=
      by
        intro h_contra
        rw [h_contra] at hAeq
        contradiction
    -- H ⊆ A であることを示す
    have A_mem_elements : A ∈ elements :=
      by
        rw [Finset.mem_filter]
        constructor
        case left => simp
        simp [hA, hAne]

    -- 矛盾を導くために、H のカードが elements の sup と等しいことを示す
    have hH_max_card : H.card = elements.sup (λ s=> s.card) :=
      by
        apply le_antisymm
        exact Finset.le_sup H_mem
        apply Finset.sup_le
        intros s hs
        rw [Finset.mem_filter] at hs

        let ⟨hs_mem, hs_prop⟩ := hs
        have hs_sets : sf.sets s := by
          simp at hs_prop
          exact (And.left hs_prop)
        have hs_ne_univ : s ≠ Finset.univ := by
          simp at hs_prop
          exact (And.right hs_prop)
        rw [Finset.mem_powerset] at hs
        have hs_subset : s ⊆ Finset.univ := hs.1
        have hs_in_elements0: sf.sets s && decide (s ≠ Finset.univ):= by
          simp [hs_sets, hs_ne_univ]

        have hs_in_elements : s ∈ elements := by
          exact Finset.mem_filter.mpr ⟨hs_mem, hs_in_elements0⟩
        --have hcard_le : s.card ≤ H.card := H_max s hs_in_elements
        --exact hcard_le
        rw [←Finset.nonempty_iff_ne_empty] at hne
        have h_le_sup : s.card ≤ elements.sup (λ s => s.card) :=
        all_elements_le_sup_card hne s hs_in_elements
        have h_H_eq_sup : H.card = elements.sup (λ s => s.card) := by
          apply le_antisymm
          exact Finset.le_sup H_mem

          apply Finset.sup_le
          intros s hs
          rw [Finset.mem_filter] at hs
          let ⟨hs_mem, hs_prop⟩ := hs
          have hs_sets : sf.sets s := by simp at hs_prop; exact hs_prop.1
          have hs_ne_univ : s ≠ Finset.univ := by simp at hs_prop; exact hs_prop.2
          rw [Finset.mem_powerset] at hs_mem
          --have hs_subset : s ⊆ Finset.univ := hs_mem
          --have hs_subset2 : Finset.card s ≤ Fintype.card U :=
          --  by exact Finset.card_le_card hs_subset
          have hhh:  ∀ x ∈ elements, x.card ≤ H.card := by
            rw [H_max]
            exact all_elements_le_sup_card hne
          apply hhh
          simp [elements]
          exact ⟨hs_sets, hs_ne_univ⟩

        --exact Finset.sup_le (λ t ht => H_max t ht)
        rw [h_H_eq_sup]
        exact h_le_sup

    by_cases hAeqH : A = H
    -- A = H の場合
    exact Or.inl hAeqH
    -- A ≠ H の場合
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

    --ゴールはA = H ∨ A = Finset.univでもどちらでもないケースで矛盾になることを言うはず。
    --h_card_lt : H.card < A.card
    --H.card = elements.sup fun s => s.card
    --A ∈ elements
    have h_contra : H.card < H.card := by
      rw [hH_max_card] at h_card_lt
      have h_le_sup : A.card ≤ elements.sup (λ s => s.card) := Finset.le_sup A_mem_elements
      rw [hH_max_card]
      omega
    omega

---上の極大hyperedgeの存在の証明はうまくいったが、長い部分を外に出したり、証明を短くしてみたり検討してみた。
---長い部分hH_max_cardを外に出すことを考えた。自動証明で短くなった。
lemma max_card_eq_sup {U : Type} [DecidableEq U] [Fintype U] (elements : Finset (Finset U)) (H : Finset U) (H_mem : H ∈ elements) (H_max : (∀ s, s ∈ elements → s.card ≤ H.card)) :
  H.card = elements.sup (λ s => s.card) :=
  by
    apply le_antisymm
    · apply Finset.le_sup
      simp_all only
    · simp_all only [Finset.sup_le_iff, implies_true]

--Ideal集合族に対する極大hyperedgeの存在定理をChatGPT Plusに短く書き換えてもらった。
--この言明だとしては、全体集合が許される。その場合は、Ideal集合族は冪集合になる。このことも示す必要があるかも。
--この定理の言明は修正の必要がある。H=Finset.univの場合がいつでも取れてしまう。
--Ideal集合族が冪集合であるか、Hとして、全体集合以外をとることができるかという言明にするか。
theorem exists_maximal_hyperedge2 (sf : IdealFamily U) :
  ∃ H : Finset U, sf.sets H ∧ ∀ ⦃A : Finset U⦄, sf.sets A → H ⊆ A → (A = H ∨ A = Finset.univ) :=
by
  --考えている集合族としては、全体集合を除いて考えている。
  let elements := Finset.filter (λ s => sf.sets s && s ≠ Finset.univ) (Finset.powerset Finset.univ)
  have hne : elements.Nonempty :=
    by
      use ∅
      rw [Finset.mem_filter]
      constructor
      simp [sf.empty_mem]
      simp [elements, elements, Finset.filter_eq']
      constructor
      exacts [sf.empty_mem, empty_ne_univ]

  rw [Finset.nonempty_iff_ne_empty] at hne
  obtain ⟨H, H_mem, H_max⟩ := exists_max_card elements hne
  use H
  have H_mem_elements : H ∈ elements := H_mem
  have H_mem_def : H ∈ Finset.filter (λ s => sf.sets s && s ≠ Finset.univ) (Finset.powerset Finset.univ) := H_mem_elements
  have H_mem_filter : sf.sets H ∧ H ≠ Finset.univ :=
    by simp [Finset.mem_filter] at H_mem_def; exact H_mem_def
  constructor
  exact H_mem_filter.1
  intros A hA hHA
  by_cases hAeq : A = Finset.univ
  simp [hAeq]
  have hAne : A ≠ Finset.univ :=
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
    rename_i inst inst_1 inst_2
    intro s a
    simp_all only [ne_eq, decide_not, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, not_false_eq_true, and_self, true_and, elements]
    --obtain ⟨left, right⟩ := H_mem_filter
    obtain ⟨left_1, right_1⟩ := a
    apply Finset.le_sup
    simp_all only [Finset.mem_filter, Finset.mem_univ, not_false_eq_true, and_self]

  --使うのはl_card_ltとmax_card_eq_supとA_mem_elements : A ∈ elements
  have h_contra : H.card < H.card :=
    by
      rw [max_card_eq_sup elements H H_mem (H_max2 H_max)] at h_card_lt
      have h_le_sup : A.card ≤ elements.sup (λ s => s.card) := Finset.le_sup A_mem_elements
      rw [max_card_eq_sup]
      linarith
      omega
      linarith
      --意外と上の3つのどれかをコメントアウトすると証明が通らなくなる。
  omega

-- 頂点を含むhyperedgeから頂点を含まないhyperedgeへの単射。単射になることはあとで示す。
-- H = Finset.univのときの移り先が違う。
-- imsの引数は定義にはいらないかも。これをつけるのであれば、x notin Gの条件をつけたほうがいいかも。
def map_hyperedge (sf : IdealFamily U) (x : U) (G: Finset U)(_: is_maximal_hyperedge sf G)(H : Finset U) : Finset U :=
  if H = Finset.univ then G
  else Finset.erase H x

-- x notin Gのときにmap_hyperedgeで移った先がhyperedgeであることの定理。
-- map_hyperedgeがsf.setsの元であることを証明する
theorem map_hyperedge_is_hyperedge (sf : IdealFamily U) (x : U) (G : Finset U) (imh : is_maximal_hyperedge sf G) (H : Finset U) :
  sf.sets H → x ∉ G → sf.sets (map_hyperedge sf x G imh H) :=
by
  intros hH _
  unfold map_hyperedge
  by_cases h_univ : H = Finset.univ
  -- H = Finset.univ の場合
  case pos =>
    rw [h_univ]
    simp [hH]
    exact imh.1
  -- H ≠ Finset.univ の場合
  case neg =>
    have h_subset : (Finset.erase H x) ⊆ H := Finset.erase_subset x H
    have hH' : sf.sets (Finset.erase H x) :=
      by
        --let HX := (Finset.erase H x)
        exact sf.down_closed hH h_subset
        ---(down_closed : ∀ {A B : Finset U}, sets B → A ⊆ B → sets A)

    have hH'' : sf.sets (Finset.erase H x) :=
      by
        rename_i inst _ _
        simp_all only
    rw [if_neg h_univ]
    exact hH''

--def sorry_proof (sf : IdealFamily U) (H : Finset U) : x ∉ H :=
--  by sorry
--このあたりから単射性の証明に使った補題の証明になる。
-- 極大hyperedgeに1点付け加えるとhyperedgeにならないか全体集合になるかの証明
lemma insert_union_eq (G : Finset U) (x : U) : insert x (G ∪ {x}) = G ∪ {x} :=
  by
    simp_all only [Finset.mem_union, Finset.mem_singleton, or_true, Finset.insert_eq_of_mem]

lemma ssubset_insert (G : Finset U) (x : U) : x ∉ G → G ⊂ G ∪ {x} :=
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

lemma G_union_x_hyperedge_or_univ (sf : IdealFamily U) (x : U) (G : Finset U) (imh : is_maximal_hyperedge sf G) :
  x ∉ G → ¬sf.sets (G ∪ {x}) ∨ G ∪ {x} = Finset.univ :=
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
      exact G_max G_subset
    -- G ∪ {x} がハイパーエッジでない場合
    · left
      exact h

lemma erase_insert_eq (H G : Finset U) (x : U) : x ∈ H → Finset.erase H x = G → H = G ∪ {x} :=
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

-- H1が全体集合の場合の矛盾を示す補助定理
-- Hはxを含む。
-- Hはhyperedgeである。
-- Hが全体集合でなければ、Gには映らないことを示す。
lemma map_hyperedge_univ_eq (sf : IdealFamily U) (x : U) (G : Finset U) (imh : is_maximal_hyperedge sf G) (H : Finset U) :
  x ∈ H → sf.sets H → x ∉ G → H ≠ Finset.univ → map_hyperedge sf x G imh H ≠ G :=
  by
    intro hxH  -- x ∈ Hであることを仮定
    intro hsxH  -- Hがハイパーエッジであることを仮定
    intro hxG  -- x ∉ Gであることを仮定
    intro hH   -- Hが全体集合でないことを仮定
    unfold map_hyperedge
    by_cases h : H = Finset.univ
    · contradiction  -- Hが全体集合である場合、仮定に矛盾
    · simp [h]  -- Hが全体集合でない場合。
      intro h_eq
      -- Hからxを取り除いた結果がGであると仮定
      -- H = G ∪ {x}であることを示す
      have H_eq : H = G ∪ {x} := erase_insert_eq H G x hxH h_eq
      -- G ∪ {x}がハイパーエッジでないか全体集合であることを示す
      have H_hyperedge_or_univ := G_union_x_hyperedge_or_univ sf x G imh hxG
      match H_hyperedge_or_univ with
      | Or.inl h_not_hyperedge =>
        -- H = G ∪ {x} がハイパーエッジでない場合の処理
        -- Hはhyperedgeであることと矛盾。
        rw [←H_eq] at h_not_hyperedge
        contradiction
      | Or.inr h_univ =>
        -- H = G ∪ {x} が全体集合の場合の処理
        rw [←H_eq] at h_univ
        contradiction

-- 非全体集合同士の結果が等しい場合の条件を示す補助定理
lemma map_hyperedge_nonuniv_eq (sf : IdealFamily U) (x : U) (G : Finset U) (imh : is_maximal_hyperedge sf G) (H1 H2 : Finset U) :
x ∈ H1→ x ∈ H2 → x ∉ G → H1 ≠ Finset.univ → H2 ≠ Finset.univ → map_hyperedge sf x G imh H1 = map_hyperedge sf x G imh H2 → Finset.erase H1 x = Finset.erase H2 x :=
  by
    -- 仮定を導入
    intro _ _ _ hH1 hH2 h_map
    -- map_hyperedgeの定義を展開し、H1とH2が全体集合でない場合の処理を行う
    unfold map_hyperedge at h_map
    rw [if_neg hH1, if_neg hH2] at h_map
    -- 結果が等しいことからFinset.erase H1 x = Finset.erase H2 xであることを結論づける
    exact h_map

theorem subtype_eq_of_val_eq (sf : IdealFamily U) (x : U) (H1 H2 : { H // sf.sets H = true ∧ x ∈ H }) :
  H1.1 = H2.1 → H1 = H2 :=
  by
   --rename_i inst inst_1 _
   intro a
   obtain ⟨val, property⟩ := H1
   obtain ⟨val_1, property_1⟩ := H2
   obtain ⟨left, right⟩ := property
   obtain ⟨left_1, right_1⟩ := property_1
   simp_all only

lemma set_eq_of_erase_eq {A B : Finset U} {x : U} (hxA : x ∈ A) (hxB : x ∈ B) (h : Finset.erase A x = Finset.erase B x) : A = B :=
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

--theorem map_hyperedge_is_hyperedge (sf : IdealFamily U) (x : U) (G : Finset U) (imh : is_maximal_hyperedge sf G) (H : Finset U) :
--  sf.sets H → x ∉ G → sf.sets (map_hyperedge sf x G imh H) :=
--Gが極大である証明は、mapの定義にそもそも必要か。
--証明が完了するためには、そのようなGの存在が必要なので補題の引数にするといいかも。

--def map_hyperedge (sf : IdealFamily U) (x : U) (G: Finset U)(imh: is_maximal_hyperedge sf G)(H : Finset U) : Finset U :=
--  if H = Finset.univ then G else Finset.erase H x

lemma map_hyperedge_injective (sf : IdealFamily U) (x : U) (G: Finset U) (imh : is_maximal_hyperedge sf G)  :
  x ∉ G → Function.Injective (λ H : {H // sf.sets H ∧ x ∈ H} => map_hyperedge sf x G imh H.1):=
  by
    intro hxG  -- x ∉ Gであることを仮定
    -- 単射性の証明
    intros H1 H2 h_map  -- 任意のH1, H2に対して、map_hyperedgeの結果が等しいことを仮定
    --H1 H2 : { H // sf.sets H = true ∧ x ∈ H }
    --h_map : (fun H => map_hyperedge sf x G imh ↑H) H1 = (fun H => map_hyperedge sf x G imh ↑H) H2
    -- map_hyperedge_nonuniv_eqを利用して、Finset.erase H1.1 x = Finset.erase H2.1 xであることを示す

    contrapose! h_map
    have hmap1: H1.1 ≠ H2.1 := by
       --subtype_eq_of_val_eqを使う。
       --H1.1 = H2.1を仮定して矛盾を導く。
       --h_mapはH1 ≠ H2である。
        intro h_contra
        --have hh12: H1.1=H2.1 ∧ x ∈ H1.1 ∧ x ∈ H2.1 := by
        --  obtain ⟨val1, property_1,property_11⟩ := H1
        --  obtain ⟨val2, property_2,property_21⟩ := H2
        --  have eq: val1 = val2 := by exact h_contra
        --  exact ⟨eq, property_11, property_21⟩
        have hh122: H1 = H2 := by
          exact Subtype.ext h_contra
        contradiction
    ----移った先が違うことを示す。
    by_cases h_univ1 : H1.1 = Finset.univ
    -- H1.1 = Finset.univ の場合
    have h_univ12 : H2.1 ≠ Finset.univ :=
      by
          simp_all only [ne_eq]
          obtain ⟨val, property⟩ := H1
          obtain ⟨val_1, property_1⟩ := H2
          obtain ⟨left, right⟩ := property
          obtain ⟨left_1, right_1⟩ := property_1
          simp_all only [Subtype.mk.injEq, not_false_eq_true]
          subst h_univ1
          simp_all only [Finset.mem_univ]
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [Finset.mem_univ, not_true_eq_false]

    --#check H2.2.1
    --#check H2.2.2
    have value1:map_hyperedge sf x G imh H1.1 = G := by
      simp [map_hyperedge, h_univ1]
    rw [value1]
    exact (map_hyperedge_univ_eq sf x G imh H2.1 H2.2.2 H2.2.1 hxG h_univ12).symm
    --lemma map_hyperedge_univ_eq (sf : IdealFamily U) (x : U) (G : Finset U) (imh : is_maximal_hyperedge sf G) (H : Finset U) :
    --x ∈ H → sf.sets H → x ∉ G → H ≠ Finset.univ → map_hyperedge sf x G imh H ≠ G
    --を利用。
    --def map_hyperedge (sf : IdealFamily U) (x : U) (G: Finset U)(imh: is_maximal_hyperedge sf G)(H : Finset U) : Finset U :=
    -- if H = Finset.univ then G else Finset.erase H x
    --H_1とH_2が異なるときに、h_mapが成り立たないことを示す。対偶。
    --H1.1 ≠ Finset.univの場合の証明をする。
    by_cases h_univ2: H2.1 = Finset.univ
    have value2:map_hyperedge sf x G imh H2.1 = G := by
      simp [map_hyperedge, h_univ2]
    -- H2.1 ≠ Finset.univ の場合
    -- map_hyperedge_nonuniv_eqを使う。
    rw [value2]
    exact map_hyperedge_univ_eq sf x G imh H1.1 H1.2.2 H1.2.1 hxG h_univ1

    -- H1.1 ≠ Finset.univ かつ H2.1 ≠ Finset.univ の場合
    -- map_hyperedge_nonuniv_eqを使う。
    --h_mapはH1 ≠ H2からmap_hyperedge sf x G imh ↑H1 ≠ map_hyperedge sf x G imh ↑H2を示す。
    contrapose! h_map
    have result: H1.1.erase x = H2.1.erase x := ((map_hyperedge_nonuniv_eq sf x G imh H1.1 H2.1) H1.2.2 H2.2.2 hxG h_univ1 h_univ2) h_map
    -- H1.1.erase x = H2.1.erase x から H1.1 = H2.1 であることを示す。h1.2.2:x in H1.1 と h2.2.2:x in H2.1 が必要。
    -- ¬↑H2 = Finset.univ
    have h_erase_eq : H1.1 = H2.1 :=
      by
        exact set_eq_of_erase_eq  H1.2.2 H2.2.2 result

    exact subtype_eq_of_val_eq sf x H1 H2 h_erase_eq


    --lemma map_hyperedge_nonuniv_eq (sf : IdealFamily U) (x : U) (G : Finset U) (imh : is_maximal_hyperedge sf G) (H1 H2 : Finset U) :
    --x ∈ H1→ x ∈ H2 → x ∉ G → H1 ≠ Finset.univ → H2 ≠ Finset.univ → map_hyperedge sf x G imh H1 = map_hyperedge sf x G imh H2 → Finset.erase H1 x = Finset.erase H2 x :=

--上をchatGPTが書き換えたもの。短くなった。
lemma map_hyperedge_injective2 (sf : IdealFamily U) (x : U) (G: Finset U) (imh : is_maximal_hyperedge sf G) :
  x ∉ G → Function.Injective (λ H : {H // sf.sets H ∧ x ∈ H} => map_hyperedge sf x G imh H.1) :=
by
  intro hxG
  intros H1 H2 h_map
  contrapose! h_map
  have hmap1: H1.1 ≠ H2.1 := by
    intro h_contra
    --使ってないかも。
    --have _: H1.1 = H2.1 ∧ x ∈ H1.1 ∧ x ∈ H2.1 := by
    --  obtain ⟨val1, property_1, property_11⟩ := H1
    --  obtain ⟨val2, property_2, property_21⟩ := H2
    --  have eq: val1 = val2 := by exact h_contra
    --  exact ⟨eq, property_11, property_21⟩
    have hh122: H1 = H2 := by exact Subtype.ext h_contra
    contradiction
  by_cases h_univ1 : H1.1 = Finset.univ
  · have h_univ2 : H2.1 ≠ Finset.univ := by
      simp_all only [ne_eq]
      obtain ⟨val, property⟩ := H1
      obtain ⟨val_1, property_1⟩ := H2
      obtain ⟨left, right⟩ := property
      obtain ⟨left_1, right_1⟩ := property_1
      simp_all only [Subtype.mk.injEq, not_false_eq_true]
      subst h_univ1
      simp_all only [Finset.mem_univ]
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [Finset.mem_univ, not_true_eq_false]
    have value1 : map_hyperedge sf x G imh H1.1 = G := by simp [map_hyperedge, h_univ1]
    rw [value1]
    exact (map_hyperedge_univ_eq sf x G imh H2.1 H2.2.2 H2.2.1 hxG h_univ2).symm
  by_cases h_univ2 : H2.1 = Finset.univ
  · have value2 : map_hyperedge sf x G imh H2.1 = G := by simp [map_hyperedge, h_univ2]
    rw [value2]
    exact map_hyperedge_univ_eq sf x G imh H1.1 H1.2.2 H1.2.1 hxG h_univ1
  contrapose! h_map
  have result : H1.1.erase x = H2.1.erase x := ((map_hyperedge_nonuniv_eq sf x G imh H1.1 H2.1) H1.2.2 H2.2.2 hxG h_univ1 h_univ2) h_map
  have h_erase_eq : H1.1 = H2.1 := by exact set_eq_of_erase_eq H1.2.2 H2.2.2 result
  exact Subtype.ext h_erase_eq
-----------------------------------------------------------------
  variable {α : Type*} [DecidableEq α] {A B : Finset α}

lemma exists_element_not_in_subset (h : A ⊂ B) : ∃ x ∈ B, x ∉ A :=
  by
    -- 真部分集合の定義から、A ⊆ B かつ A ≠ B を得る
    obtain ⟨hAB, hneq⟩ := ssubset_iff_subset_ne.mp h
    -- 対偶法を使用して証明する
    by_contra h'
    -- h' を反転させる
    push_neg at h'
    -- h' が成り立つと仮定すると、A = B となる
    have h_eq : A = B := antisymm hAB h'
    --subset.antisymmは見つからなかった。
    --同様な関数にSet.eq_of_subset_of_subsetがあるが、Finsetにはない。
    -- これは A ≠ B という仮定に反する
    exact hneq h_eq
