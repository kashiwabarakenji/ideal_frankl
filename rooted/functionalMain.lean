-- The main theorem concerning functionals is contained in `functional_family_average_rare`.
-- All the key theorems at each stage branch out from here.

-- `functionalCommon.lean` collects the basic definitions. `Setup` is also defined here.
-- For the preorder on `Setup`, the discussion is in `functionalTreePreorder`.
-- `Setup2` introduces a partial order on the setoid defined in `Setup`, and is defined in `functionalTreePartialOrder`.
-- The preorder `Setup2` has the same strength of assumptions as `Setup`.

-- `functionalTreeIdeal` discusses `Setup2` in terms of closed set families.
-- `Setup_spo` is defined in `functionalSPO`. Since no preorder appears here, it is more abstract.

-- However, looking back now, if we had allowed the original `f` to map to the same element,
-- we might not have needed to distinguish between `Setup` and `Setup_spo`.

-- `functionalIdealrare` is also within the `Setup_spo` framework.
-- `Setup_spo2` incorporates the condition that each element has exactly one parent,
-- making it slightly stronger than `Setup_spo`.

-- The original condition is `Setup_spo2`, but theorems that hold under slightly weaker conditions are proved for `Setup_spo`.

-- `functionalTraceIdeal` reduces the problem to theorems in the partial order framework via tracing.
-- The `functionalPartial` series deals with theorems in the partial order framework; see there for details.

-- If we were to rename: `Setup` could be called `Setup_pre`.
-- `Setup_spo` can remain as is.
-- `Setup_po` can also stay as is.

-- As a refactoring, it might be better to remove the initial `valid` condition and formalize it.
-- Doing so might eliminate the need for `Setup_spo` altogether.

import Mathlib.Data.Finset.Basic
import Init.WF
import Mathlib.Order.WellFoundedSet
import LeanCopilot
import rooted.CommonDefinition
import rooted.functionalCommon
import rooted.functionalPartial
import rooted.functionalExcess
import rooted.functionalPartialOne
import rooted.functionalDirectProduct2

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

lemma setup_po_average_rare_card_one (t : Setup_po α) (card1 : t.V.card = 1) :
  (po_closuresystem t).toSetFamily.normalized_degree_sum ≤ 0 := by
  let ceo := (@card_eq_one _ t.V).mp card1
  obtain ⟨x, _hx⟩ := ceo

  dsimp [ SetFamily.normalized_degree_sum]
  simp

  have h_sets : ∀ ss : Finset α,
      (po_closuresystem t).sets ss ↔ ss = ∅ ∨ ss = t.V := by
    intro ss
    constructor
    · intro h
      have hsub : ss ⊆ t.V := by
        dsimp [po_closuresystem] at h
        exact h.1
      have : ss = ∅ ∨ ss = t.V := by
        simp_all only
          [Finset.card_singleton,
           Finset.subset_singleton_iff,
           Nat.lt_one_iff,
           card_eq_zero,
           card_eq_one]
      exact this
    · intro h
      cases h
      case inl hl =>
        -- case of ss = ∅
        rw [hl]
        dsimp [po_closuresystem]
        simp
      case inr hr =>
        -- case of ss = {x}
        rw [hr]
        simp_all only
          [Finset.card_singleton,
           Finset.subset_singleton_iff,
           Nat.lt_one_iff,
           card_eq_zero,
           card_eq_one]
        subst hr
        simp [po_closuresystem]
        simp_all only [Finset.mem_singleton, le_refl, imp_self, implies_true, and_self]

  -- total_size_of_hyperedges = 1
  have h_total : (po_closuresystem t).total_size_of_hyperedges = 1 := by
    dsimp [po_closuresystem] at h_sets
    dsimp [SetFamily.total_size_of_hyperedges]
    simp_all only [h_sets]
    -- {∅, {x}}
    have h :
      filter (fun s => s = ∅ ∨ s = {x}) ({x} : Finset α).powerset = {∅, {x}} := by
      simp_all only
        [Finset.subset_singleton_iff,
         Finset.mem_singleton,
         Nat.lt_one_iff,
         card_eq_zero,
         card_eq_one]
      simp_all only [singleton_inj, exists_eq', Subtype.forall, Finset.mem_singleton, le_refl, imp_self, implies_true,
        and_true]
      ext a : 1
      simp_all only [mem_filter, Finset.mem_powerset, Finset.subset_singleton_iff, and_self, Finset.mem_insert,
        Finset.mem_singleton]

    dsimp [po_closuresystem]
    simp_all only [Finset.card_singleton, Finset.subset_singleton_iff, Subtype.forall, Finset.mem_singleton, le_refl,
      imp_self, implies_true, and_true, Finset.card_empty, sum_insert_of_eq_zero_if_notMem, sum_singleton,
      Nat.cast_one]

  -- number_of_hyperedges = 2
  have h_num : (po_closuresystem t).number_of_hyperedges = 2 := by
    dsimp [SetFamily.number_of_hyperedges]
    -- ground.powerset = {∅, {x}}
    have : (po_closuresystem t).ground.powerset = {∅, {x}} := by
      dsimp [po_closuresystem] at h_sets
      simp_all only
        [Finset.subset_singleton_iff,
         Finset.mem_singleton,
         Nat.lt_one_iff,
         card_eq_zero,
         card_eq_one]
      dsimp [po_closuresystem]
      rw [_hx]
      exact rfl
    rw [this]
    dsimp [po_closuresystem]
    -- {∅, {x}}
    have h :
      filter
        (fun ss =>
          ss ⊆ t.V ∧
          ∀ v : { x // x ∈ t.V }, v.val ∈ ss → ∀ w : { x // x ∈ t.V }, t.po.le w v → w.val ∈ ss)
        ({∅, {x}} : Finset (Finset α)) = {∅, {x}} := by
      simp_all only
        [Finset.subset_singleton_iff,
         Finset.mem_singleton,
         Nat.lt_one_iff,
         card_eq_zero,
         card_eq_one]
      simp [filter_true_of_mem]
      simp_all only [singleton_inj, exists_eq', Finset.mem_singleton, le_refl, imp_self, implies_true, and_true]
      simp [filter_true_of_mem]
    simp_all only
      [Finset.subset_singleton_iff,
       Finset.mem_singleton,
       Nat.lt_one_iff,
       card_eq_zero,
       card_eq_one]
    rfl

  rw [h_total, h_num]
  apply Int.ge_of_eq
  apply congrArg (HMul.hMul 2)
  apply congrArg Nat.cast
  exact card1

theorem setup_po_average_rare (s_orig:Setup_po α): (po_closuresystem s_orig).normalized_degree_sum ≤ 0 :=
by
  let P : ℕ → Prop := fun n =>
    ∀ t : Setup_po α,
      t.V.card = n →
      (po_closuresystem t).toSetFamily.normalized_degree_sum ≤ 0

  have hP : ∀ n, P n := by
    intro n
    -- strong recursion on `n`
    induction' n using Nat.strongRec with n ih
    intro t ht_card

    by_cases h_le_one : t.V.card ≤ 1
    · -- base case
      have : t.V.card = 1 :=
      by
        exact le_antisymm h_le_one (one_le_card.mpr t.nonemp)
      exact setup_po_average_rare_card_one t this

    ----------------------------------------------------------------
    -- inductive case |V| ≥ 2
    ----------------------------------------------------------------
    · have nontriv : 2 ≤ t.V.card := Nat.succ_le_of_lt (Nat.lt_of_not_ge h_le_one)

      -- the number of quotient classes
      by_cases h_one : numClasses (proj_setoid t) = 1

      --------------------------------------------------------------
      --  (1) class number = 1  ― reduce ground by Trace
      --------------------------------------------------------------
      · -- take a maximal element
        obtain ⟨x, hx⟩ := t.nonemp --quotient_exists t
        let mx := proj_max t ⟨x, hx⟩
        have hmx : po_maximal t mx := by
          exact proj_max_maximal t ⟨x, hx⟩

        -- nds
        have h_nds_le_trace :=
          normalized_degree_sum_gt t h_one mx hmx nontriv
        -- reducing ground
        have h_card_lt :
            (po_trace t mx hmx nontriv).V.card < t.V.card :=
          trace_one_ground_card t mx hmx nontriv
        -- by strong induction hypothesis, trace side nds ≤ 0
        have h_nds_trace :=
          ih _ (by
                have : (po_trace t mx hmx nontriv).V.card < n := by
                  have := h_card_lt
                  simpa [ht_card] using this
                exact this) _ (by
                  -- card of trace  = card,  reflexive rewrite
                  rfl)

        exact h_nds_le_trace.trans h_nds_trace

      --------------------------------------------------------------
      --  (2) the case of class number ≥ 2 ― devided by comp/excl
      --------------------------------------------------------------
      · -- ≥ 2
        have h_ge_two : numClasses (proj_setoid t) ≥ 2 := by
          have h_pos : 0 < numClasses (proj_setoid t) := numClasses_pos t
          have : 1 ≤ numClasses (proj_setoid t) := Nat.succ_le_of_lt h_pos
          apply Nat.succ_le_of_lt
          exact Nat.lt_of_le_of_ne h_pos fun a => h_one (id (Eq.symm a))

        -- take an appropriate class q
        obtain  ⟨q : Quotient (proj_setoid t)⟩ := quotient_exists t

        have h_comp_card :=
          directProduct_comp_excel_ground_c t q h_ge_two
        have h_excl_card :=
          directProduct_comp_excel_ground_e t q h_ge_two

        -- IH is devided into comp and excl
        have h_nds_comp :
            (po_closuresystem (comp_po t q)).toSetFamily.normalized_degree_sum ≤ 0 := by
          have h_lt : (comp_po t q).V.card < n := by
            have : (comp_po t q).V.card < t.V.card := h_comp_card
            simpa [ht_card] using this
          exact (ih _ h_lt) _ rfl

        have h_nds_excl :
            (po_closuresystem (excl_po t q h_ge_two)).toSetFamily.normalized_degree_sum ≤ 0 := by
          have h_lt : (excl_po t q h_ge_two).V.card < n := by
            have : (excl_po t q h_ge_two).V.card < t.V.card := h_excl_card
            simpa [ht_card] using this
          exact (ih _ h_lt) _ rfl

        -- composing of comp and excl
        exact directProduct_nds t q h_ge_two h_nds_comp h_nds_excl
  exact hP (#s_orig.V) s_orig rfl

--Note that only here we use $s₀$ instead of $s$ as the initial $s$, because $s$ will vary in the induction.
--Since we are using trace_ideal_nds_increase, the assumption needs to be Setup_spo2 instead of Setup_spo.
theorem setup_spo2_average_rare (s₀ :Setup_spo2 α): (spo_closuresystem s₀.toSetup_spo).normalized_degree_sum ≤ 0 :=
by
-- The proof of this theorem uses strong induction on the value of `excess`.
-- The base case `excess = 0` corresponds to `setup_po_average_rare`.
-- To prove that correspondence, we use `excess_zero`.

-- Using
-- lemma trace_excess_decrease (s : Setup_spo2 α) (x : s.V) (hx : (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2) :
--   excess (setup_trace_spo2 s x hx) = excess s - 1 := by
-- we show that `excess` decreases.

-- theorem trace_ideal_nds_increase (s : Setup_spo2 α) (x : s.V) (hx : (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2)

-- The overall structure of the proof was designed with the help of ChatGPT o3, using `WellFoundedOn`.

  let r : Setup_spo2 α → Setup_spo2 α → Prop :=
  fun s t => excess s.toSetup_spo < excess t.toSetup_spo

  have wf_r : WellFounded r := by simpa [r] using
    (measure (fun s : Setup_spo2 α => excess s.toSetup_spo)).wf

  let wf_on : (univ : Set (Setup_spo2 α)).WellFoundedOn r :=
    WellFounded.wellFoundedOn wf_r

  apply Set.WellFoundedOn.induction wf_on (x := s₀) (hx := Set.mem_univ s₀)
  intro s mem_s ih

  by_cases h0 : excess s.toSetup_spo = 0
  · --base case
    -- all classses have size 1.
    have h1 : ∀ q, (classOf s.toSetup_spo q).card = 1 := by
      apply excess_zero s.toSetup_spo
      exact h0
    let s_po := po_ideal_system_from_allone _ h1
    let spa := setup_po_average_rare s_po
    rw [←po_ideal_system_eq]
    simp_all only [not_lt_zero', IsEmpty.forall_iff, implies_true, ge_iff_le]
    exact spa

  · -- inductive step ：excess s > 0
    have hpos : 0 < excess s.toSetup_spo := by
      simp_all only [Set.mem_univ, gt_iff_lt, ge_iff_le, forall_const, r]
      omega

    obtain ⟨q, hq⟩ := exists_q_card_ge_two_of_excess_pos s.toSetup_spo hpos

    have :@Quotient.mk _ s.setoid q.out = q :=
      by
        simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true, ge_iff_le, Quotient.out_eq]
    rw [←this] at hq

    let s' := setup_trace_spo2 s q.out hq

    have h_ex_s' : excess s'.toSetup_spo = excess s.toSetup_spo - 1 :=
      trace_excess_decrease s.toSetup_spo q.out hq

    have h_nds :
      (spo_closuresystem s.toSetup_spo).normalized_degree_sum
        ≤ (spo_closuresystem s'.toSetup_spo).normalized_degree_sum :=
    by
      dsimp [s']
      exact trace_ideal_nds_increase2 s q.out hq

    have h_rel : r s' s := by
      dsimp [r]
      rw [h_ex_s']
      simp_all only [Set.mem_univ, gt_iff_lt, ge_iff_le, forall_const, Quotient.out_eq, tsub_lt_self_iff,
        Nat.lt_one_iff, pos_of_gt, and_self, s', r]

    have ih_s' :
      (spo_closuresystem s'.toSetup_spo).normalized_degree_sum ≤ 0 :=
      ih s' (by simp) h_rel

    calc
      (spo_closuresystem s.toSetup_spo).normalized_degree_sum
          ≤ (spo_closuresystem s'.toSetup_spo).normalized_degree_sum := h_nds
      _ ≤ 0 := ih_s'

-- The main theorem in the form using `setup`.
-- This theorem can be reduced to `setup_spo2_average_rare`, so no induction is needed and it can be proved directly.
-- The theorems being used, such as `excl`, appear in `TreePartial` and `SPO2`.

lemma setup_average_rare (s:Setup α): (pre_closuresystem s).normalized_degree_sum ≤ 0 :=
by
  let s2 :=  (Setup_to_Setup2 s)
  let s_spo := setup2_induces_spo s2
  have : s2.toSetup = s :=
  by
    rfl
  rw [←this]
  rw [Preorder_eq_PartialOrder s2] --TreeIdeal
  rw [Setup_spo_eq_PartialOrder s2] --TreeIdeal
  exact setup_spo2_average_rare s_spo

--the main theorem without setup
theorem functional_family_average_rare (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty) :
  (rootedsetToClosureSystem (rootedset_onestem_eachvertex_V V f valid nonemp)).normalized_degree_sum ≤ 0 :=
by
  let rs := rootedset_onestem_eachvertex_V V f valid nonemp
  set pre := size_one_preorder V f valid nonemp with h_pre
  set st := @setoid_preorder V pre with h_st
  let s := Setup.mk V nonemp f valid pre h_pre st h_st
  let sns := setup_average_rare s
  rw [pre_closuresystem_eq_lem] at sns
  dsimp [pre_closuresystem2] at sns
  dsimp [rootedset_from_setup] at sns
  exact sns
