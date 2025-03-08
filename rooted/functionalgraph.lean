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
