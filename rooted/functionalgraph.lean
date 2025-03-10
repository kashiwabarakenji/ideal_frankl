import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import LeanCopilot

open Finset Set Classical

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
set_option linter.unusedSectionVars false

/-- f-compatible の定義 -/
def fCompatible (f : V → V) (F : Finset V) : Prop :=
  ∀ v, f v ∈ F → v ∈ F

/-- f-compatible 集合の全体 -/
noncomputable def fCompatibles (f : V → V) : Finset (Finset V) :=
  univ.filter (fCompatible f)

/-! ### 平均次数と平均サイズについて -/

/-- 各頂点 v の次数：
    その頂点を含む f-compatible 集合の個数  -/
def degree (F : Finset (Finset V)) (v : V) : ℕ :=
  (F.filter (λ I => v ∈ I)).card

/-- 集合族 F の平均次数 -/
def avg_degree (F : Finset (Finset V)) : ℚ :=
  (∑ v in univ, degree F v) / (Fintype.card V : ℚ)

/-- 集合族 F の各要素の大きさの平均 -/
def avg_size (F : Finset (Finset V)) : ℚ :=
  (∑ I in F, I.card) / (F.card : ℚ)

/-- 補題1: double counting の原理
    頂点の次数の総和と、各集合の要素数の総和は一致する。 -/
theorem double_counting (F : Finset (Finset V)) :
  (∑ v ∈ univ, degree F v) = (∑ I in F, I.card) :=
sorry

/-- 補題1（平均次数と平均サイズの同値性）:
    集合族の平均次数が (|V|)/2 以下であることと、
    平均サイズが (|V|)/2 以下であることは同値である。
    （※F.nonempty を仮定） -/
theorem avg_degree_iff_avg_size (F : Finset (Finset V)) (hF : F.Nonempty) :
  avg_degree F ≤ (Fintype.card V : ℚ) / 2 ↔ avg_size F ≤ (Fintype.card V : ℚ) / 2 :=
sorry

/-! ### 順序集合（Poset）に関する補題 -/

variable {P : Type} [Fintype P] [PartialOrder P][DecidableEq P]

/-- 極大元の定義
    m が極大であるとは、任意の x に対して m < x なら矛盾が生じる、という性質。 -/
def is_maximal (m : P) : Prop :=
∀ x : P, m < x → False

/- P の全ての極大元の集合。 -/
noncomputable def maximalElements : Finset P :=
univ.filter is_maximal

theorem unique_maximal_above (x y z : P)
  (hxy : x ≤ y) (hy_max : is_maximal y)
  (hxz : x ≤ z) (hz_max : is_maximal z) : y = z :=
sorry
--同値類になることを示した方がいいかも。代表元として、極大元がとれる。

/-- 各ノードがたかだか 1 つの親（直前の上位ノード）を持つことを表す性質 -/
def atMostOneParent (P : Type) [PartialOrder P] : Prop :=
  ∀ v : P, ∀ u₁ u₂ : P, u₁ < v → u₂ < v → u₁ = u₂

/-- 極大元 m に対して、その単元ideal（m 以下の全要素の集合）を定義する。 -/
noncomputable def principalIdeal (m : P) : Finset P :=
({x : P | x ≤ m} : Set P).toFinset

/-- 補題: もし y と z が異なる極大元であれば、
    それぞれの単元idealは互いに交わらない。 -/
theorem principalIdeal_disjoint {y z : P}
  (ap: atMostOneParent P) (hy_max : is_maximal y) (hz_max : is_maximal z)
  (h : y ≠ z) : (principalIdeal y) ∩ (principalIdeal z) = ∅ :=
sorry

/-- 有限な poset では、任意の要素 x に対して、x ≤ m かつ m が極大である m が存在する。 -/
theorem exists_maximal_above (x : P) : ∃ m : P, is_maximal m ∧ x ≤ m :=
sorry

/-- 各 x に対して、x の上にある極大元を選ぶ（存在定理より classical.choice で選んでいる）。 -/
noncomputable def maxAbove (x : P) : P :=
Classical.choose (exists_maximal_above x)

theorem maxAbove_spec (x : P) : is_maximal (maxAbove x) ∧ x ≤ maxAbove x :=
Classical.choose_spec (exists_maximal_above x)

/-- 補題: もし m が極大ならば、m の上にある極大元は m 自身である。
    （有限 poset では、極大元は下閉性より自明に m ≤ m かつ m の上に m 以外は存在しない。） -/
theorem maxAbove_idempotent (m : P) (h : is_maximal m) : maxAbove m = m :=
sorry

/-- 各 x に対して、maxAbove (x) は x の上にある極大元であり、さらに極大元であるため、
    maxAbove (maxAbove x) = maxAbove x が成立する。 -/
theorem maxAbove_self (x : P) : maxAbove (maxAbove x) = maxAbove x :=
by
  -- maxAbove_spec (maxAbove x) により、maxAbove x ≤ maxAbove (maxAbove x) とあるが、maxAbove x は極大
  have hmax := (maxAbove_spec x).1
  apply maxAbove_idempotent
  exact hmax


/-- x と y を、x の上にある極大元が等しいことによって同値とする同値関係の定義。 -/
def maxEquiv (x y : P) : Prop :=
maxAbove x = maxAbove y

instance maxEquivSetoid : Setoid P where
  r := maxEquiv
  iseqv :=  @Equivalence.mk _ maxEquiv
    -- reflexivity
    λ x => by rfl
    -- symmetry
    λ h => by
      unfold maxEquiv
      simpa [maxAbove] using h.symm
    -- transitivity
    λ hxy hyz => by exact hxy.trans hyz--eq.trans hxy hyz


/-- 同値関係 maxEquiv により、各同値類の代表として maxAbove x が取れる。
    すなわち、任意の x ∈ P に対して、maxAbove x は極大であり、かつ x ~ maxAbove x が成立する。 -/
theorem maxAbove_is_repr (x : P) : maxEquiv x (maxAbove x) :=
by
  -- maxAbove x と x は同値、すなわち maxAbove x = maxAbove (maxAbove x) であるが、
  -- これは maxAbove_self により示される。
  dsimp [maxEquiv]
  exact (maxAbove_self x).symm

/-- 結果として、maxEquiv による同値類の各代表元は、その同値類に属する極大元となる。 -/
theorem each_class_has_maximal_repr (x : P) : ∀ y, maxEquiv x y → maxAbove x = maxAbove y :=
fun y h=> h

/- この同値関係によって、P は同値類に分解され、各同値類の代表元として maxAbove x が選べる。 -/
/-
def maxEquivQuotient : Type :=
  Quotient (maxEquivSetoid)
-/

-- ここで、各同値類の代表として maxAbove x を選ぶ写像を定義することもできるが、基本的には
-- Quotient.mk を用いて同値類の扱いが可能である。


--------------


/-- 補題2: 単元idealによる順序idealの個数下界
    各 v ∈ P に対して、単元 ideal { u | u ≤ v } は一意であるため、
    順序ideal の個数は少なくとも |P| 個存在する。 -/
theorem principal_ideals_injective (h : atMostOneParent P) :
  Function.Injective (λ v : P => { u : P // u ≤ v }) :=
sorry

/-- 補題3: 台集合の拡張が平均次数に与える影響
    台集合のサイズを n-1 から n に拡張した場合、
    平均次数（各頂点の次数の平均）は上昇しない。 -/
theorem extension_avg_degree_nonincreasing
  {V' : Type} [Fintype V'] [DecidableEq V']
  (i : V → V')
  (F : Finset (Finset V))
  (F_ext : Finset (Finset V')) -- F_ext は F の拡張版とする
  : avg_degree F_ext ≤ avg_degree F :=
sorry

/-- 補題4: 連結な半順序集合における極大ノードの一意性
    連結な poset で、各ノードがたかだか 1 つの親を持つならば、
    極大なノードはただひとつ存在し、その単元idealは全体集合となる。 -/
theorem connected_maximal_unique
  (h_conn : ∀ x y : P, ∃ z, x ≤ z ∧ y ≤ z)
  (h : atMostOneParent P) :
  ∃! m : P, ∀ x : P, x ≤ m :=
sorry

/- 補題5: 非連結な半順序集合における平均順序ideal大きさの評価
    各連結成分で平均がその成分の大きさの半分以下であれば、
    全体としても平均は |P|/2 以下となる。 -/
/-部分的に半順序集合を考える。
theorem disconnected_avg_bound
  (h_comp : ∀ (S : Finset P), (* S が連結成分ならばその平均順序ideal大きさは |S|/2 以下 *) True)
  : True :=
sorry
-/

/- 補題6: 半順序集合における順序idealの平均大きさの上界
    各ノードがたかだか 1 つの親を持つ poset では、
    順序ideal の平均大きさは |P|/2 以下である。 -/
/-
theorem average_ideal_size_bound
  (h : atMostOneParent P)
  (I : Finset (Finset P)) (* I を poset P の順序ideal の全体とする *)
  : avg_size I ≤ (fintype.card P : ℚ) / 2 :=
sorry
-/

/-- 補題7: 極大ノードの rare 性
    poset P において、任意の極大元 m（すなわち、∀ x, ¬ (m < x) を満たす m）は、
    m を含む順序ideal の個数が全順序ideal の個数の半分以下である。 -/
theorem maximal_element_rare
  (h : atMostOneParent P)
  (m : P) (h_max : ∀ x : P, ¬ (m < x))
  : (fintype.card { I : Finset P | m ∈ I ∧ (* I が順序ideal であることの条件 *) True })
    ≤ (fintype.card { I : Finset P | (* I が順序ideal であることの条件 *) True }) / 2 :=
sorry

/-! ### f-compatible 集合と順序ideal の同型性、およびパラレル化操作 -/

/-- 補題8:
    有限集合 V 上の写像 f : V → V に対し、
    「もし f v ∈ I ならば v ∈ I」という性質を満たす集合族（f-compatible 集合）は、
    関係 v < f v により生成される前順序の順序ideal と一対一対応する。
    さらに、ideal の大きさが 2 以上となる同値類は、
    同値な要素をまとめたときの極大元に対応する。 -/
theorem f_compatible_ideal_iso (f : V → V) :
  (* fCompatibles f と、v < f v によって生成される順序ideal との間に同型が存在することを示す。 *)
  sorry :=
sorry

/-- 補題9: rare な頂点のパラレル化と平均次数の変化
    poset において、rare な頂点 x を、x と同じ含有条件を持つ新たな頂点 y としてパラレル化した場合、
    全体の平均次数（または平均サイズ）は上昇しない（場合によっては低下する）。 -/
theorem parallelization_avg_nonincreasing
  (F : Finset (Finset V))
  (x : V)
  (h_rare : (* x が rare であることの条件 *) True)
  : True :=
sorry

/-! ### 定理: ideal の平均大きさの上界 -/

/-- 定理:
    有限集合 V 上の写像 f : V → V に対し、
    「もし f v ∈ I ならば v ∈ I」という性質を満たす集合族（すなわち f-compatible 集合）、
    すなわち前順序の順序ideal の平均サイズは、
    台集合 V の大きさの半分以下である。 -/
theorem ideal_average_bound (f : V → V) :
  avg_size (fCompatibles f) ≤ (fintype.card V : ℚ) / 2 :=
sorry

omit [DecidableEq V] in
lemma fCompatibles_nonempty (f : V → V) : (fCompatibles f).Nonempty :=
  by simp [fCompatibles]; exact ⟨∅, by simp [fCompatible]⟩



omit [DecidableEq V] in
lemma ground_is_fCompatible (f : V → V) : fCompatible f univ := by simp [fCompatible]

omit [DecidableEq V] in
omit [Fintype V] in
lemma empty_is_fCompatible (f : V → V) : fCompatible f ∅ := by simp [fCompatible]

omit [Fintype V] in
theorem Finset.powerset_singleton (x : V) :
    ({x} : Finset V).powerset = {∅, {x}} :=
  rfl

theorem mem_finset_pair_eq {α : Type*} [DecidableEq α] {A B v : α} :
    v ∈ ({A, B} : Finset α) ↔ v = A ∨ v = B := by
  simp



/-- 基底ケース: |V| = 1 -/
lemma base_case_avg_one (f : V → V) (hV : Fintype.card V = 1) :
  2 * (∑ F ∈ fCompatibles f, F.card) = Fintype.card V * (fCompatibles f).card := by
  -- V has exactly one element v
  obtain ⟨v, hhv⟩ := Fintype.card_eq_one_iff.mp hV
  -- Since f is a function from V to V, f(v) must be v
  have univ_v: Finset.univ = {v}:= by
    ext x : 1
    simp_all only [Finset.mem_univ]
    simp_all only [Finset.mem_singleton]

  -- Therefore, f is a constant function

  have h_fv : f v = v := by
    have : v ∈ Finset.univ := Finset.mem_univ v
    simp_all
  -- The only f-compatible subsets are ∅ and {v}
  have h_compat_emp : fCompatible f ∅ := by simp [fCompatible]
  have h_compat_v : fCompatible f {v} := by
    simp_all only
    intro v' hv'
    simp_all only [Finset.mem_singleton]
  -- Therefore, fCompatibles f = {∅, {v}}
  have h_fCompatibles : fCompatibles f = {∅, {v}} := by
    ext F
    simp [fCompatibles, fCompatible, h_fv]
    apply Iff.intro
    · intro h
      by_cases F = ∅
      ·
        rename_i h_2
        subst h_2
        simp_all only [Finset.not_mem_empty, implies_true, true_or]
      · by_cases F = {v}
        ·
          rename_i h_3
          subst h_3
          simp_all only [Finset.mem_singleton, imp_self, implies_true, Finset.singleton_ne_empty, not_false_eq_true,
            or_true]
        · --show F = ∅ ∨ F = {v}
          have : F ∈ Finset.univ.powerset := by
            rw [Finset.mem_powerset]
            exact Finset.subset_univ F
          rw [univ_v] at this
          have : F ∈ ({∅, ({v}:Finset V)}:Finset (Finset V)) := by
            simp_all only [implies_true, Finset.mem_powerset, Finset.subset_singleton_iff, or_self]
          simp_all
    · intro h
      intro v' hv'
      simp_all only
  -- Calculate left-hand side: 2 * (0 + 1) = 2
  -- Calculate right-hand side: 1 * 2 = 2
  simp [h_fCompatibles, Fintype.card_subtype_compl, hV]
  simp_all only
  rfl

/-- 非全射ならば、rangeが不足する -/
lemma exists_non_image {f : V → V} (hf : ¬ Function.Surjective f) :
  ∃ u : V, u ∉ range f :=
by
  simp_all only [Set.mem_range, not_exists]
  contrapose! hf
  exact hf
/-- fの制限 -/
lemma f_restrict_ne {u : V} (f : V → V) (hu : u ∉ range f) (v : {x : V // x ≠ u}) :
  f v.val ≠ u := fun h ↦ hu ⟨v.val, h⟩

def f_restrict (u : V) (f : V → V) (hu : u ∉ range f) :
  {v : V // v ≠ u} → {v : V // v ≠ u} := fun v ↦
  ⟨f v.val, f_restrict_ne f hu v⟩

/-- fCompatible for subtype -/
def fCompatible_subtype (f : {v : V // v ≠ u} → {v : V // v ≠ u}) (F : Finset {v : V // v ≠ u}) : Prop :=
  ∀ v, f v ∈ F → v ∈ F

/-- fCompatibles for subtype -/
noncomputable def fCompatibles_subtype (f : {v : V // v ≠ u} → {v : V // v ≠ u})  : Finset (Finset {v : V // v ≠ u}) :=
  Finset.univ.filter (fCompatible_subtype f)

/-- 非全射の帰納段階の主張 -/
lemma non_surj_ind_step (f : V → V) (hf : ¬ Function.Surjective f)
  (hV : 2 ≤ Fintype.card V) (u : V) (hu : u ∉ range f)
  (IH : 2 * (∑ F ∈ fCompatibles_subtype (f_restrict u f hu), F.card)
          ≤ Fintype.card {v : V // v ≠ u} * (fCompatibles_subtype (f_restrict u f hu)).card) :
  2 * (∑ F in fCompatibles f, F.card) ≤ Fintype.card V * (fCompatibles f).card :=
  sorry

/-- 全射の場合のサイクル分解による証明 -/
lemma surjective_case_avg (f : V → V) (hf : Function.Surjective f) :
  2 * (∑ F in fCompatibles f, F.card) = Fintype.card V * (fCompatibles f).card :=
  sorry

/-- メインの定理の帰納法による証明 -/
theorem avg_fCompatible_le_half (f : V → V) :
  2 * (∑ F ∈ fCompatibles f, F.card) ≤ Fintype.card V * (fCompatibles f).card := by
  --let n := Fintype.card V
  induction Fintype.card V using Nat.strong_induction_on with
  | h n IH =>
    by_cases h_n1 : n = 1
    · have h_card : Fintype.card V = 1 := by
        have : Fintype.card V = n := by
          sorry
        subst this
        simp_all only [Nat.lt_one_iff, zero_mul, nonpos_iff_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero,
          sum_eq_zero_iff, card_eq_zero, false_or, forall_eq]
      rw [h_n1]
      simp
      have eq1 := base_case_avg_one f h_card
      rw [h_card] at eq1
      rw [eq1]
      simp

    · have h_card : Fintype.card V = n := by
        sorry  -- Fintype.card V is definitionally n here
      have h_n_ge : 2 ≤ n := by
        cases n with
        | zero =>
            have :(Finset.univ:Finset V) ≠ ∅ := by simp_all only [not_lt_zero', IsEmpty.forall_iff,
              implies_true, zero_ne_one, not_false_eq_true, Fintype.card_ne_zero]
            simp_all only [not_lt_zero', IsEmpty.forall_iff, implies_true, zero_ne_one, not_false_eq_true,
              Fintype.card_ne_zero]
        | succ n =>
          cases n with
          | zero => contradiction
          | succ n => simp_all only [add_left_eq_self, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
            not_false_eq_true, le_add_iff_nonneg_left, zero_le]
      by_cases hf : Function.Surjective f
      · have h_bijective : Function.Bijective f := by
         --have : Function.Injective f := Function.Surjective.injective_of_fintype (by rfl) hf
         exact Function.Surjective.bijective_of_finite hf
        --fがbijectiveであるならば、#fCompatibles f は、同値類の分割になる。補題のケース。
        rw [←h_card]
        let sca := surjective_case_avg f hf
        subst h_card
        simp_all only [Multiset.bijective_iff_map_univ_eq_univ, le_refl, sca]

      · obtain ⟨u, hu⟩ := exists_non_image hf
        let V' := { v : V // v ≠ u }
        have h_cardV' : Fintype.card V - 1 = Fintype.card V' :=
        by
          simp_all only [Set.mem_range, not_exists, ne_eq, Fintype.card_subtype_compl, Fintype.card_unique, V']
        have IH' : 2 * (∑ F ∈ fCompatibles_subtype (f_restrict u f hu), F.card)
                    ≤ (n - 1) * (fCompatibles_subtype (f_restrict u f hu)).card :=
        by
          show 2 * ∑ F ∈ fCompatibles_subtype (f_restrict u f hu), #F ≤ (n - 1) * #(fCompatibles_subtype (f_restrict u f hu))
          --IH : ∀ m < n, 2 * ∑ F ∈ fCompatibles f, #F ≤ m * #(fCompatibles f)
          let IH'' := IH (n - 1) (Nat.sub_lt (Nat.one_le_of_lt h_n_ge) zero_lt_one)
          have :(fCompatibles_subtype (f_restrict u f hu)).card = (fCompatibles (f_restrict u f hu)).card := by
            subst h_card
            simp_all only [ne_eq, Fintype.card_subtype_compl, Fintype.card_unique, V']
            rfl
          have :#(fCompatibles_subtype (f_restrict u f hu)) = #(fCompatibles (f_restrict u f hu)) := by
            subst h_card
            simp_all only [ne_eq, Fintype.card_subtype_compl, Fintype.card_unique, V']
          rw [this]
          have :(fCompatibles_subtype (f_restrict u f hu)).sum Finset.card = (fCompatibles (f_restrict u f hu)).sum Finset.card :=
          by
            subst h_card
            simp_all only [ne_eq, Fintype.card_subtype_compl, Fintype.card_unique, V']
            rfl
          have :∑ F ∈ fCompatibles_subtype (f_restrict u f hu), #F = (∑
            F ∈ fCompatibles (f_restrict u f hu), F.card) :=
          by
            subst h_card
            simp_all only [ne_eq, Fintype.card_subtype_compl, Fintype.card_unique, V']
          rw [this]
          convert IH''
          · show ∑ F ∈ fCompatibles (f_restrict u f hu), #F = ∑ F ∈ fCompatibles f, #F
            sorry
          · show #(fCompatibles (f_restrict u f hu)) = #(fCompatibles f)
            dsimp [f_restrict, fCompatibles, fCompatible]
            show #(filter (fCompatible (f_restrict u f hu)) Finset.univ) = #(filter (fCompatible f) Finset.univ)
            sorry

        rw [h_card] at h_cardV'
        have IH'' : 2 * (∑ F ∈ fCompatibles_subtype (f_restrict u f hu), F.card)
                    ≤ Fintype.card {v : V // v ≠ u} * (fCompatibles_subtype (f_restrict u f hu)).card :=
          by rwa [h_cardV'] at IH'
        rw [←h_card]
        exact non_surj_ind_step f hf (by linarith) u hu IH''


/- 平均値としての表示
theorem avg_fCompatible_card_le_half (f : V → V) :
  ((∑ F in fCompatibles f, F.card : ℚ) / (fCompatibles f).card)
    ≤ (Fintype.card V : ℚ) / 2 := by
  rw [div_le_iff₀ (Nat.cast_pos.mpr (card_pos.mpr (fCompatibles_nonempty f)))]
  exact_mod_cast avg_fCompatible_le_half f
-/

/- 全射の場合に等号が成り立つ -/

/- Vのタイプがおかしい。
lemma singleton_of_card_one {α : Type*} [Fintype α] {V : Finset α} {v : α}
    (hV : Fintype.card V = 1) (hv : v ∈ V) : V = {v} :=
by
  obtain ⟨v', hv'⟩ := Fintype.card_eq_one_iff.mp hV
  have : v' = v := by
    apply Finset.eq_of_mem_singleton
    simp
    simp_all only [Fintype.card_coe, Subtype.forall]
    obtain ⟨val, property⟩ := v'
    simp_all only [Subtype.mk.injEq]
  subst this
  simp_all only [Fintype.card_coe, Subtype.forall, coe_mem]
  obtain ⟨val, property⟩ := v'
  simp_all only [Subtype.mk.injEq]
  ext a : 1
  simp_all only [Finset.mem_singleton]
  apply Iff.intro
  · intro a_1
    simp_all only
  · intro a_1
    subst a_1
    simp_all only
-/
