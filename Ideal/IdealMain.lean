--Ideal集合族が平均abundantにならないことの証明。メイン定理。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import Ideal.IdealDeletion
import Ideal.IdealRare
import Ideal.IdealSum
import Ideal.IdealNumbers
import Ideal.IdealDegreeOne
import Ideal.IdealFin
import Ideal.IdealDegOneMain
import LeanCopilot
set_option maxHeartbeats 1000000

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

--メイン定理の帰納法のベースケース。大きさ2の場合の証明。
theorem basecase : P 2 := by
  constructor
  simp_all only [ge_iff_le]
  simp_all only [le_refl]
  intros F ground_card
  dsimp [normalized_degree_sum]
  simp_all only [ge_iff_le, tsub_le_iff_right, zero_add]
  dsimp [total_size_of_hyperedges]
  dsimp [number_of_hyperedges]
  have gr: F.ground = {0, 1} := by
    simp_all only [Fin.isValue]
    have or2: ∀ (a:Fin 2), a = 0 ∨ a = 1 := by
      intro a
      cases a
      simp_all only [Fin.isValue]
      omega
    apply Finset.eq_of_subset_of_card_le
    simp_all only [Fin.isValue]
    intro a
    intro _
    simp_all only [Fin.isValue, Finset.mem_insert, Finset.mem_singleton]
    simp_all only [Fin.isValue, Finset.mem_singleton, zero_ne_one, not_false_eq_true, Finset.card_insert_of_not_mem,
      Finset.card_singleton, Nat.reduceAdd, le_refl]
  rw [gr]
  simp
  simp_all only [Fin.isValue, Finset.mem_singleton, zero_ne_one, not_false_eq_true, Finset.card_insert_of_not_mem,
    Finset.card_singleton, Nat.reduceAdd]

  have hasground: F.sets {0, 1}:= by
    rw [←gr]
    exact F.has_ground
  have hasempty: F.sets ∅ := by
    exact F.has_empty
  have pow: (Finset.univ : Finset (Fin 2)).powerset = {{0,1}, {0}, {1}, ∅} := by
    simp_all only [Fin.isValue, Finset.powerset_univ]
    decide
  let zeroone : Finset (Fin 2) := {0, 1}
  have pow2: zeroone.powerset = {{0,1}, {0}, {1}, ∅} := by
    simp_all only [Fin.isValue]
    simp_all only [Fin.isValue, Finset.powerset_univ, zeroone]
    exact pow
  let zp :=  zeroone.powerset
  rw [pow2]

  have zeroonedisj: Disjoint ({zeroone, ∅} : Finset (Finset (Fin 2))) ({{0}, {1}} : Finset (Finset (Fin 2))) := by
    simp_all only [Fin.isValue]
    simp_all only [Fin.isValue, Finset.disjoint_iff_inter_eq_empty, zeroone]
    decide

  have zeroonedisj2: Disjoint ({0} : (Finset (Fin 2))) ({1} :  (Finset (Fin 2))) := by
    simp_all only [Fin.isValue]
    simp_all only [Fin.isValue, Finset.disjoint_iff_inter_eq_empty, zeroone]
    decide

  have zeroonedisj3: Disjoint (Finset.filter (fun x => F.sets {x}) {0}) (Finset.filter (fun x => F.sets {x}) {1}) := by
    simp_all only [Fin.isValue]
    simp_all only [Fin.isValue, Finset.disjoint_iff_inter_eq_empty, zeroone]
    simp_all only [Fin.isValue, Finset.powerset_univ, Finset.mem_singleton, one_ne_zero, not_false_eq_true,
      Finset.inter_singleton_of_not_mem]
    ext1 a
    simp_all only [Fin.isValue, Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton, Finset.not_mem_empty,
      iff_false, not_and, zero_ne_one, false_and, not_false_eq_true, and_imp, implies_true]

  have zeroonedisj4: Disjoint ({0, 1}:(Finset (Fin 2))) ∅ := by
    simp_all only [Fin.isValue, Finset.powerset_univ, Finset.disjoint_insert_right, Finset.mem_insert,
      Finset.mem_singleton, Finset.singleton_ne_empty, or_false, Finset.disjoint_singleton_right, one_ne_zero,
      not_false_eq_true, Finset.image_insert, Finset.image_singleton, Finset.image_empty, Finset.disjoint_empty_right,
      zeroone]

  have zeroonedisj5: Disjoint ({{0, 1}}:Finset (Finset (Fin 2))) {∅} := by
    simp_all only [Fin.isValue, Finset.powerset_univ, Finset.disjoint_insert_right, Finset.mem_insert,
      Finset.mem_singleton, Finset.singleton_ne_empty, or_false, Finset.disjoint_singleton_right, one_ne_zero,
      not_false_eq_true, Finset.image_insert, Finset.image_singleton, Finset.image_empty, Finset.disjoint_empty_right,
      zeroone]
    obtain ⟨left, right⟩ := zeroonedisj
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [Fin.isValue, Finset.mem_insert, Finset.insert_eq_self, Finset.mem_singleton, zero_ne_one, or_true,
      Finset.insert_eq_of_mem]
    contradiction

  have zerooneunion: ({{0, 1}, ∅} : Finset (Finset (Fin 2))) ∪ ({{0}, {1}} : Finset (Finset (Fin 2))) = {{0, 1}, {0}, {1}, ∅} := by
    simp_all only [Fin.isValue]
    simp_all only [Fin.isValue,  zeroone]
    decide

  have zerooneunion2: ({0} : Finset (Fin 2)) ∪ ({1} : Finset (Fin 2)) = {0, 1} := by
    simp_all only [Fin.isValue]
    decide

  have zerooneunion3: ({{0, 1}, ∅} : Finset (Finset (Fin 2))) = {{0, 1}} ∪  {∅} := by
    simp_all only [Fin.isValue, Finset.powerset_univ, Finset.disjoint_insert_right, Finset.mem_insert,
      Finset.mem_singleton, Finset.singleton_ne_empty, or_false, Finset.disjoint_singleton_right, one_ne_zero,
      not_false_eq_true, Finset.union_insert, Finset.insert_union, zeroone]
    rfl

  have leftside: ∑ x in Finset.filter F.sets (Finset.powerset zeroone), x.card = 2 + (Finset.card (Finset.filter (λ x => F.sets {x}) zeroone)) := by
    rw [pow2]
    let dist:= filter_union_distrib F.sets ({{0,1},∅}) ({{0},{1}})
    simp at dist

    let distsum := filter_union_sum F.sets ({{0,1},∅}) ({{0},{1}}) zeroonedisj
    let filtereq := filter_union_eq F.sets ({{0,1},∅}) ({{0},{1}}) --うまくいってない？{{0, 1}, ∅} ∪ {{0}, {1}}= {{0, 1}, {0}, {1}, ∅} が成り立つはず。
    simp at filtereq
    rw [zerooneunion] at distsum
    rw [←distsum]

    have goal1:  ∑ x ∈ Finset.filter F.sets {{0, 1}, ∅}, x.card = 2 := by
      simp_all only [Fin.isValue]
      simp_all only [Fin.isValue, Finset.powerset_univ, zeroone, zp]
      simp_all only [Fin.isValue, Finset.disjoint_insert_right, Finset.mem_insert, Finset.mem_singleton,
        Finset.singleton_ne_empty, or_false, Finset.disjoint_singleton_right, Finset.union_insert,
        Finset.insert_union]
      obtain ⟨left, right⟩ := zeroonedisj
      simp [Finset.filter_true_of_mem, *]
      simp_all only [Fin.isValue, one_ne_zero, not_false_eq_true, Finset.image_insert, Finset.image_singleton,
        Finset.image_empty, Finset.disjoint_empty_right, Finset.union_assoc, Finset.mem_union, Finset.mem_singleton,
        Finset.singleton_ne_empty, or_false]
      rfl

    have goal2: ∑ x ∈ Finset.filter F.sets {{0}, {1}}, x.card = (Finset.filter (fun x => F.sets {x}) zeroone).card := by
      rw [Finset.sum_filter, Finset.card_filter]
      simp
      dsimp [zeroone]
      simp_all only [Fin.isValue]
      let result0 := filter_union_eq0 (fun x => F.sets {x}) {0} {1}
      --have eqn1: ({0} : Finset (Fin 2)) ∪ ({1} : Finset (Fin 2)) = {0, 1} := by
      --  simp_all only [Fin.isValue]

      rw [zerooneunion2] at result0
      rw [result0]
      have term1: (if F.sets {0} then 1 else 0) = (Finset.filter (fun x => F.sets {x}) {0}).card := by
        simp
        by_cases h01: F.sets {0}
        · case pos =>
          simp_all only [Fin.isValue, Finset.powerset_univ, Finset.disjoint_insert_right, Finset.mem_insert,
            Finset.mem_singleton, Finset.singleton_ne_empty, or_false, Finset.disjoint_singleton_right,
            Finset.union_insert, Finset.insert_union, ↓reduceIte, zeroone]
          --obtain ⟨left, right⟩ := zeroonedisj
          symm
          simp [result0, Finset.filter_singleton]
          simp_all only [Fin.isValue, ↓reduceIte, Finset.card_singleton]
        · case neg =>
          simp_all only [Fin.isValue, Finset.powerset_univ, Finset.disjoint_insert_right, Finset.mem_insert,
            Finset.mem_singleton, Finset.singleton_ne_empty, or_false, Finset.disjoint_singleton_right,
            Finset.union_insert, Finset.insert_union, ↓reduceIte, zeroone]
          symm
          simp_all only [Fin.isValue, Finset.card_eq_zero]
          ext1 a
          simp_all only [Fin.isValue, Finset.mem_filter, Finset.mem_singleton, Finset.not_mem_empty, iff_false,
            not_and, not_false_eq_true, implies_true]

      have term2: (if F.sets {1} then 1 else 0) = (Finset.filter (fun x => F.sets {x}) {1}).card := by
        simp
        by_cases h10: F.sets {1}
        · case pos =>
          simp_all only [Fin.isValue, Finset.powerset_univ, Finset.disjoint_insert_right, Finset.mem_insert,
            Finset.mem_singleton, Finset.singleton_ne_empty, or_false, Finset.disjoint_singleton_right,
            Finset.union_insert, Finset.insert_union, ↓reduceIte, zeroone]
          symm
          simp [result0, Finset.filter_singleton]
          simp_all only [Fin.isValue, ↓reduceIte, Finset.card_singleton]
        · case neg =>
          simp_all only [Fin.isValue, Finset.powerset_univ, Finset.disjoint_insert_right, Finset.mem_insert,
            Finset.mem_singleton, Finset.singleton_ne_empty, or_false, Finset.disjoint_singleton_right,
            Finset.union_insert, Finset.insert_union, ↓reduceIte, zeroone]
          symm
          simp_all only [Fin.isValue, Finset.card_eq_zero]
          ext1 a
          simp_all only [Fin.isValue, Finset.mem_filter, Finset.mem_singleton, Finset.not_mem_empty, iff_false,
            not_and, not_false_eq_true, implies_true]

      rw [term1, term2]

      --#check Finset.card_union_of_disjoint zeroonedisj2
      have eqn2: (Finset.filter (fun x => F.sets {x}) {0}).card + (Finset.filter (fun x => F.sets {x}) {1}).card = (Finset.filter (fun x => F.sets {x}) zeroone).card := by
        have result0 := filter_union_eq0 (fun x => F.sets {x}) {0} {1}
        rw [zerooneunion2] at result0
        symm
        dsimp [zeroone]
        rw [result0]
        --goalが　 (A ∪ B).card　= A.card + B.card
        --haveI : DecidablePred (λ x => F.sets {x}) := inferInstance
        rw [Finset.union_comm]
        exact Finset.card_union_of_disjoint zeroonedisj3

      dsimp [zeroone] at eqn2 ⊢
      rw [eqn2]
      rw [←(filter_union_eq0 (fun x => F.sets {x}) {0} {1})]

      rw [zerooneunion2]

    simp_all only [Fin.isValue, Finset.powerset_univ, Finset.disjoint_insert_right, Finset.mem_insert,
      Finset.mem_singleton, Finset.singleton_ne_empty, or_false, Finset.disjoint_singleton_right, one_ne_zero,
      not_false_eq_true, Finset.union_insert, Finset.insert_union, zeroone]

  rw [pow2] at leftside
  --rw [leftside] 表面上一致しているが、一致しない。
  have rightside: (Finset.filter F.sets zeroone.powerset).card =  2 + (Finset.card (Finset.filter (λ s => F.sets s) {{0},{1}})) := by
    have rightside_lem: (Finset.filter F.sets zeroone.powerset).card = (Finset.card (Finset.filter (λ s => F.sets s) {zeroone, ∅})) + (Finset.card (Finset.filter (λ s => F.sets s) {{0},{1}})) := by
      rw [pow2]
      rw [←zerooneunion]
      --lemma filter_union_eq (P : Finset α → Prop) [DecidablePred P] (A B : Finset (Finset α)) : (A ∪ B).filter P = (A.filter P) ∪ (B.filter P)
      rw [filter_union_eq F.sets {{0, 1}, ∅} {{0}, {1}}]
      simp_all only [Fin.isValue, Finset.powerset_univ, Finset.disjoint_insert_right, Finset.mem_insert,
        Finset.mem_singleton, Finset.singleton_ne_empty, or_false, Finset.disjoint_singleton_right, one_ne_zero,
        not_false_eq_true, Finset.union_insert, Finset.insert_union, zeroone]
      obtain ⟨left, right⟩ := zeroonedisj
      rw [Finset.card_union_of_disjoint]
      symm
      apply Finset.disjoint_filter_filter
      simp_all only [Fin.isValue, Finset.union_assoc, Finset.mem_union, Finset.mem_singleton,
        Finset.singleton_ne_empty, or_false, Finset.disjoint_union_right, Finset.disjoint_singleton_right,
        Finset.mem_insert, Finset.insert_eq_self, zero_ne_one, not_or]
      apply And.intro
      · apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [Fin.isValue, Finset.mem_insert, Finset.singleton_inj, zero_ne_one, Finset.mem_singleton,
          Finset.singleton_ne_empty, or_self, or_false, Finset.insert_eq_of_mem, Finset.mem_union,
          Finset.union_eq_left, Finset.subset_singleton_iff, one_ne_zero]
      · apply And.intro
        · apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [Fin.isValue, Finset.mem_insert, Finset.singleton_inj, zero_ne_one, Finset.mem_singleton,
            or_true, Finset.insert_eq_of_mem, Finset.mem_union, or_false]
          contradiction
        · apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [Fin.isValue, Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.union_idempotent]
          contradiction

    have rightside_eq2:(Finset.card (Finset.filter (λ s => F.sets s) {zeroone, ∅})) = 2:= by
      dsimp [zeroone]
      rw [zerooneunion3]
      rw [filter_union_eq F.sets {{0, 1}} {∅}]
      --#check @Finset.disjoint_filter_filter
      -- Ensure the correct usage of Finset.disjoint_filter_filter
      --Finset.disjoint_filter_filter zeroonedisj
      --#check Finset.card_union_of_disjoint (Finset.disjoint_filter_filter zeroonedisj4)
      have disjoint_filtered := (@Finset.disjoint_filter_filter _ ({{0, 1}}:Finset (Finset (Fin 2))) {∅} F.sets F.sets) zeroonedisj5
      rw [Finset.card_union_of_disjoint disjoint_filtered]
      simp
      have value2: (Finset.filter F.sets {{0, 1}}).card = 1 := by
        have assum: ∀ x∈ ({{0,1}}:Finset (Finset (Fin 2))), F.sets x := by
          intro x
          simp_all only [Fin.isValue]
          obtain ⟨val, property⟩ := x
          intro a
          simp_all only [Fin.isValue, Finset.mem_singleton]
        rw [(Finset.filter_eq_self).mpr assum]
        simp_all only [Fin.isValue, Finset.mem_singleton, forall_eq, Finset.card_singleton]
        --hasground : F.sets {0, 1}

      have value0: (Finset.filter F.sets {∅}).card = 1:= by
        --hasempty : F.sets ∅
        have assum: ∀ x∈ ({∅}:Finset (Finset (Fin 2))), F.sets x := by
          intro x
          simp_all only [Fin.isValue]
          obtain ⟨val, property⟩ := x
          intro a
          simp_all only [Fin.isValue, Finset.mem_singleton]
        rw [(Finset.filter_eq_self).mpr assum]
        simp_all only [Fin.isValue, Finset.mem_singleton, forall_eq, Finset.card_singleton]

      simp_all only [Fin.isValue, Finset.powerset_univ, Finset.disjoint_insert_right, Finset.mem_union,
        Finset.mem_singleton, Finset.singleton_ne_empty, or_false, Finset.disjoint_singleton_right, one_ne_zero,
        not_false_eq_true, Finset.image_insert, Finset.image_singleton, Finset.image_empty,
        Finset.disjoint_empty_right, Finset.union_insert, Finset.union_assoc, Nat.reduceAdd, zeroone]

    rw [rightside_lem]
    rw [rightside_eq2]

  simp_all only [Fin.isValue, Finset.powerset_univ, Finset.disjoint_insert_right, Finset.mem_union,
    Finset.mem_singleton, Finset.singleton_ne_empty, or_false, Finset.disjoint_singleton_right, one_ne_zero,
    not_false_eq_true, Finset.image_insert, Finset.image_singleton, Finset.image_empty, Finset.disjoint_empty_right,
    Finset.union_insert, Finset.union_assoc, Nat.cast_add, Nat.cast_ofNat, ge_iff_le, zeroone]
  --obtain ⟨left, right⟩ := zeroonedisj
  norm_cast
  --rw [rightside]
  rw [leftside]
  simp
  have new_goal: (Finset.filter (fun x => F.sets {x}) ({0, 1}:Finset (Fin 2))).card = (Finset.filter (fun s => F.sets s) {{0}, {1}}:Finset (Finset (Fin 2))).card:= by
    simp
    let domain := Finset.filter (fun x => F.sets {x}) ({0, 1}:Finset (Fin 2))
    let range := Finset.filter (fun s => F.sets s) {{0}, {1}}
    --let i: (x :Fin 2) → x ∈ ({0, 1}: Finset (Fin 2)) → Finset (Fin 2) := λ x _ => {x}
    let i: (x :Fin 2) → x ∈ domain → Finset (Fin 2) := λ x _ => {x}
    --let i: (Fin 2) → Finset (Fin 2) := λ x => {x}
    have hi: ∀ x (h:x ∈ domain), i x h ∈ range := by
      intro x
      intro h
      simp_all only [Fin.isValue, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.singleton_inj,
        and_self, and_imp, implies_true, exists_prop, forall_eq_or_imp, exists_eq_right, zero_ne_one, or_false,
        one_ne_zero, or_true, domain, i, range]
      simp_all only [Fin.isValue, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, and_self, domain]
    have inj: ∀ (a₁ : Fin 2) (ha₁ : a₁ ∈ domain) (a₂ : Fin 2) (ha₂ : a₂ ∈ domain), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ := by
      intro a₁ ha₁ a₂ ha₂ a
      simp_all only [Fin.isValue, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.singleton_inj,
        and_self, and_imp, implies_true, domain, i, range]
    have surj: ∀ s ∈ range, ∃ (x : Fin 2), ∃ (h : x ∈ domain), i x h = s := by
      intro s a
      simp_all only [Fin.isValue, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, and_self,
        Finset.singleton_inj, and_imp, implies_true, exists_prop, domain, i, range]
      obtain ⟨left_1, right_1⟩ := a
      cases left_1 with
      | inl h =>
        subst h
        simp_all only [Fin.isValue, Finset.singleton_inj, exists_eq_right, zero_ne_one, or_false, and_self]
      | inr h_1 =>
        subst h_1
        simp_all only [Fin.isValue, Finset.singleton_inj, exists_eq_right, one_ne_zero, or_true, and_self]


    let cardbij := @Finset.card_bij _ _ domain range i hi inj surj
    rw [cardbij]
  rw [new_goal]

  --leftsideとrightsideを使って、goalを証明する。
theorem inductive_step {n:Nat} (n_ge_two: n >= 2) (h_ind: P n) : P (n+1) := by
  -- ここでFintypeインスタンスを明示的に使用
  --have fintype_ground : Fintype F.ground := finF
  have n_ge_one : n ≥ 1 := by omega
  unfold P at h_ind ⊢
  obtain ⟨n_ge_two, h_ind⟩ := h_ind

  constructor
  simp_all only [ge_iff_le, Nat.reduceLeDiff]
  --obtain ⟨left, right⟩ := h
  --omega
  intros F ground_card
   -- n ≥ 2 から n + 1 ≥ 3 を導く
  have ground_ge_two: F.ground.card >= 2 := by
    have h1 : n + 1 ≥ 3 := Nat.succ_le_succ n_ge_two
    -- F.ground.card = n + 1 なので、F.ground.card ≥ 3
    rw [←ground_card] at h1
    -- F.ground.card ≥ 3 なので F.ground.card ≥ 2 も成立
    exact Nat.le_of_succ_le h1

  obtain ⟨v, hv⟩ := ideal_version_of_frankl_conjecture F
    --#check hv
  obtain ⟨v_in_ground, hv_right⟩ := hv

  by_cases singleton_hyperedge_have: F.sets {v}
  · case pos =>

    set Fdel := idealdeletion F v v_in_ground ground_ge_two
    have Fvx: v ∉ Fdel.ground := by
      intro h
      simp_all only [ge_iff_le]
      dsimp [Fdel] at h
      --simp_all only [Fdel]
      dsimp [idealdeletion] at h
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true]

    have ground_Fdel_card: Fdel.ground.card = n := by
      simp_all only [ge_iff_le]
      simp_all only [Fdel]
      rw [idealdeletion]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]

    have ground_delF_card_ge_one: Fdel.ground.card ≥ 1 := by
      simp_all only [ge_iff_le]

    --#check IdealFamily.deletionToN n_ge_one Fdel v Fvx ground_delF_card_ge_one
    set h_idealdeletion := IdealFamily.deletionToN n_ge_one Fdel v Fvx ground_delF_card_ge_one
    --IdealFamily (Fin (n + 1))になっているがFin nになってほしい。

    have ground_delF_card: h_idealdeletion.ground.card = n := by
      dsimp [h_idealdeletion]
      dsimp [IdealFamily.deletionToN]
      rw  [finDropCardEq n_ge_one v Fdel.ground Fvx]
      exact ground_Fdel_card

    have h_del_card: (@IdealFamily.deletionToN (Fin n) n n_ge_one (idealdeletion F v v_in_ground ground_ge_two) v Fvx
                ground_delF_card_ge_one).ground.card = n := by
      simp_all only [ge_iff_le]
      simp_all only [ge_iff_le, implies_true, imp_self, forall_true_left, Fdel, h_idealdeletion]
      exact ground_delF_card

    set Fcont :=  (contraction_ideal_family F v singleton_hyperedge_have ground_ge_two)
    have h_cont: Fcont.ground.card = n := by
      simp_all only [ge_iff_le]
      --simp_all only [contraction]
      simp_all only [ge_iff_le, implies_true, sub_left_inj, add_left_inj, add_right_inj, Fdel, Fcont]
      rw [contraction_ideal_family]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]
      rw [contraction]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]

    have h_cont2: Fcont.ground.card ≥ 1 := by
      simp_all only [ge_iff_le]

    have Fvx2: v ∉ Fcont.ground := by
      intro h
      simp_all only [ge_iff_le]
      dsimp [Fcont] at h
      simp_all only [Fcont]
      dsimp [contraction_ideal_family] at h
      dsimp [contraction] at h
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true]

    have h_cont_card: Fcont.ground.card = n := by
      simp_all only [ge_iff_le]

    have h_cont_card2: (contraction_ideal_family F v singleton_hyperedge_have ground_ge_two).ground.card = n:= by
      simp_all only [ge_iff_le]

    set h_contraction := IdealFamily.deletionToN n_ge_one Fcont v Fvx2 h_cont2
    have h_cont_card3: h_contraction.ground.card = n := by
      simp_all only [ge_iff_le]
      dsimp [h_contraction]
      dsimp [IdealFamily.deletionToN]
      rw [finDropCardEq n_ge_one v Fcont.ground Fvx2]
      exact h_cont_card

    dsimp [Fdel] at ground_Fdel_card
    --#check (h_ind h_idealdeletion) ground_delF_card
    let h_idealdeletion2 := h_ind h_idealdeletion ground_delF_card
    --#check h_ind h_contraction
    let h_contraction2 := (h_ind h_contraction) h_cont_card3

    have eq1: ideal_degree F v = degree F.toSetFamily v := by
      simp only [ideal_degree, degree]

    have eq2: ideal_family_size F = number_of_hyperedges F.toSetFamily := by
      simp only [ideal_family_size, total_size_of_hyperedges]

    simp only [ge_iff_le, tsub_le_iff_right, zero_add, Fdel, Fcont] at h_idealdeletion2 h_contraction2  ⊢
    simp only [normalized_degree_sum] at h_idealdeletion2 h_contraction2  ⊢

    rw [IdealFamily.deletionToN_number n_ge_one Fdel v Fvx ground_delF_card_ge_one] at h_idealdeletion2
    rw [IdealFamily.deletionToN_number n_ge_one Fcont v Fvx2 h_cont2] at h_contraction2
    dsimp [h_idealdeletion] at h_idealdeletion2
    dsimp [h_contraction] at h_contraction2
    rw [deletion_total] at h_idealdeletion2 h_contraction2
    dsimp [Fdel] at h_idealdeletion2
    dsimp [Fcont] at h_contraction2
    rw [h_del_card] at h_idealdeletion2

    --let total_del := (total_size_of_hyperedges ((@IdealFamily.deletionToN (Fin n) n n_ge_one Fdel v Fvx ground_delF_card_ge_one):IdealFamily (Fin n)).1)
    set total_del := total_size_of_hyperedges (idealdeletion F v v_in_ground ground_ge_two).1
    --set number_del := (number_of_hyperedges (@IdealFamily.deletionToN (Fin n) n n_ge_one Fdel v Fvx ground_delF_card_ge_one).1) with number_del
    set number_del := (number_of_hyperedges (idealdeletion F v v_in_ground ground_ge_two).1)
    --let total_cont := (total_size_of_hyperedges (@IdealFamily.deletionToN (Fin n) n n_ge_one Fcont v Fvx2 h_cont2).1)
    --set total_cont := total_size_of_hyperedges (contraction F.1 v v_in_ground ground_ge_two) with h_total_cont
    set total_cont := total_size_of_hyperedges (contraction_ideal_family F v singleton_hyperedge_have ground_ge_two).toSetFamily
    --let number_cont := (number_of_hyperedges (@IdealFamily.deletionToN (Fin n) n n_ge_one Fcont v Fvx2 h_cont2).1)
    --set number_cont := (number_of_hyperedges (contraction F.1 v v_in_ground ground_ge_two)) with h_number_cont
    set number_cont := (number_of_hyperedges (contraction_ideal_family F v singleton_hyperedge_have ground_ge_two).toSetFamily)
    set total := (total_size_of_hyperedges F.toSetFamily)
    set  number := (number_of_hyperedges F.toSetFamily)
    set degreev := (degree F.toSetFamily v)

    classical
    by_cases hv_hyperedge:(F.sets (F.ground \ {v}))
    ·   case pos =>
        have h_sum_have := (hyperedge_average_have F v v_in_ground ground_ge_two) hv_hyperedge singleton_hyperedge_have
        --have h_idealdeletion := (idealdeletion F v v_in_ground ground_ge_two)
        --#check sum_have
        let number_have :=  hyperedge_count_deletion_contraction_have_z F v v_in_ground ground_ge_two hv_hyperedge singleton_hyperedge_have

        simp only [ge_iff_le, tsub_le_iff_right, zero_add, Fdel, Fcont] at h_sum_have number_have
        simp only [normalized_degree_sum] at h_sum_have number_have

        --今になって考えてみれば、Fin nを使わずにground setの大きさで議論する方法の方が良かった。
        simp_all only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one, degreev, number,
          h_idealdeletion, Fdel, Fcont, h_contraction, total_del, number_del, total_cont, number_cont, total, number_have]
        linarith

    ·   case neg =>
        --hv_hyperedge:(F.sets (F.ground \ {v}))が成り立たないケース。singleton_hyperedge_have : ¬F.sets {v}のケースかも。どちらも未解決。
        have h_sum_none := hyperedge_average_none F v v_in_ground ground_ge_two hv_hyperedge singleton_hyperedge_have
        have number_none := hyperedge_count_deletion_contraction_none F v v_in_ground ground_ge_two hv_hyperedge singleton_hyperedge_have

        simp only [ge_iff_le, tsub_le_iff_right, zero_add, Fdel, Fcont] at h_sum_none number_none
        simp only [normalized_degree_sum] at h_sum_none number_none
        simp_all only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one, degreev, number, h_idealdeletion,
        Fdel, Fcont, h_contraction, total_del, number_del, total_cont, number_cont, total]
        linarith

  --case negがもう一つある。singleton_hyperedge_have:(F.sets {v})が成り立たないケース。
  --singleton_hyperedge_have:(F.sets {v})が成り立たないケース。tabでインデントを調整して見えるようになった。
  · case neg =>

        have h_indPn : P n := by
          unfold P
          exact ⟨n_ge_two, h_ind⟩
        exact degonemain n F v v_in_ground singleton_hyperedge_have ground_ge_two ground_card h_indPn

--ideal集合族が平均rareであることの定理。今回のプロジェクトのメイン定理。
theorem P_all (x : Nat) (hx : x ≥ 2) : P x := by
  -- x が 2 の場合は basecase を適用
  cases x with
  | zero => contradiction -- x が 0 の場合は矛盾
  | succ x =>
    cases x with
    | zero => contradiction -- x が 1 の場合も矛盾
    | succ n =>
      -- x = 2 の場合
      cases n with
      | zero => exact basecase -- x = 2 の場合は basecase を適用
      | succ m =>
        -- x = m + 3 以上の場合
        have m_ge_two : m + 2 ≥ 2 := Nat.le_add_left _ _ -- m + 2 は 2 以上
        exact inductive_step m_ge_two (P_all (m + 2) m_ge_two)
--------------
theorem ideal_implies_average_rare (F : IdealFamily α) : normalized_degree_sum F.toSetFamily <= 0 := by
  let n := F.ground.card
  have hn: Fintype.card F.ground = n:= by
    simp_all only [Fintype.card_coe, n]
  by_cases h : n ≥ 2
  case pos =>
    let pall := P_all n h
    dsimp [P] at pall
    --#check F.toSetFamily.toFinFamily
    have hn2: (toIdealFinFamily F n hn).ground.card = n := by
      simp_all only [toIdealFinFamily, hn]
      let equal :=  equal_card_fin_ideal_family F hn
      --#check equal
      have equal2: Fintype.card { x // x ∈ (toIdealFinFamily F n hn).ground } = (toIdealFinFamily F n hn).ground.card := by
        congr
        exact Fintype.card_coe (toIdealFinFamily F n hn).ground
      simp_all only [n, equal]
      obtain ⟨left, right⟩ := pall
      simp_all only [ge_iff_le, n]
      rfl

    let pa :=  pall.2 (toIdealFinFamily F n hn)
    let embedding := (Fintype.equivFinOfCardEq hn).toFun
    have hf: Function.Injective embedding := by
      simp_all only [embedding]
      exact (Fintype.equivFinOfCardEq hn).injective
    --let embedding2: Finset F.ground → Finset (Fin n) := λ S => S.image (Fintype.equivFinOfCardEq hn).toFun

    have number_eq: number_of_hyperedges (toIdealFinFamily F n hn).toSetFamily = number_of_hyperedges F.toSetFamily := by
      --simp [number_of_hyperedges, toIdealFinFamily, equal_card_fin_ideal_family]
      --theorem same_cardinality [DecidableEq α] [DecidableEq β] (hf : Function.Injective f)(hFG : ∀ (T : Finset β), T ∈ GSet ↔ ∃ (S : Finset α),S ∈ FSet ∧ T = S.image f) :
      -- FSet.card = GSet.card
      --α = Fin n, β = Finset { x// x ∈ F.ground}, f = embedding, FSet = F.ground.powerset.filter F.toSetFamily.sets, GSet = (toIdealFinFamily F n hn).ground.powerset.filter (toIdealFinFamily F n hn).toSetFamily.sets
      --#check same_cardinality
      let GSet := (toIdealFinFamily F n hn).ground.powerset.filter (toIdealFinFamily F n hn).toSetFamily.sets
      let FSet: Finset (Finset α)  := F.ground.powerset.filter (λ S => F.toSetFamily.sets S)
      let projectToGround (x: α) (hx: x ∈ F.ground) : { x:α  // x ∈ F.ground } := ⟨x, hx⟩
      --projectToGround x (Finset.mem_of_subset hS hx))  -- else F.ground.choose :  {x : α // x ∈ F.ground }
      haveI : DecidablePred (λ x => x ∈ F.ground) := inferInstance
      --let projectToGroundImage (S : Finset α)(hS: S ⊆ F.ground) : Finset { x : α // x ∈ F.ground }  := S.image (λ (xx:α) => if hx: xx ∈ S then projectToGround xx (hS hx) else ({ x : α // x ∈ F.ground }).choose (λ _ => True))
      let projectToGroundImage (S : Finset α)(hS: S ⊆ F.ground) : Finset { x : α // x ∈ F.ground }  :=F.ground.attach.filter (fun x => x.1 ∈ S)
      let projectFSetToGround (S : Finset (Finset α)) : Finset (Finset { x : α // x ∈ F.ground }) :=
        S.image (λ s => Finset.filter (λ y => ∃ (x : α) (hx : x ∈ F.ground), projectToGround x hx = y ∧ x ∈ s) (Finset.univ))
      let FSet2:Finset (Finset { x // x ∈ F.ground }) := projectFSetToGround FSet


      --#check @same_cardinality ({x // x ∈ F.ground}) (Fin n)  _ _ FSet2 GSet
      have hFG : ∀ (T : Finset (Fin n)), (toIdealFinFamily F n hn).sets T ↔ ∃ (S : Finset { x // x ∈ F.ground }), F.toSetFamily.sets (S.map (Function.Embedding.subtype _)) ∧ T = S.image embedding := by

        intro T
        simp_all only [toIdealFinFamily, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton]
        simp_all only [Equiv.toFun_as_coe, n, embedding]
        obtain ⟨left, right⟩ := pall
        simp_all only [ge_iff_le, n]
        apply Iff.intro
        · intro a
          let ⟨S, hS⟩ := a
          obtain ⟨h1, h2⟩ := hS
          cases h2
          simp_all only [Equiv.toFun_as_coe]
          --goal ∃ S_1,  F.sets (Finset.map (Function.Embedding.subtype fun x => x ∈ F.ground) S_1) ∧ Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S_1
          use S
          simp_all only [Equiv.toFun_as_coe]
          simp_all only [and_true]
          convert h1
          ext x a : 2
          simp_all only [Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right,
            exists_eq_right, Finset.mem_image]

        · intro a
          obtain ⟨w, h⟩ := a
          obtain ⟨left_1, right_1⟩ := h
          subst right_1
          have left_2 := left_1
          simp_all only
          have left_2 := left_2
          simp_all only
          have left_2 := left_2
          simp_all only
          have left_2 := left_2
          simp_all only
          convert left_2
          simp_all only [iff_true]
          have left_2 := left_2
          simp_all only
          have left_2 := left_2
          simp_all only
          have left_2 := left_2
          simp_all only
          have left_2 := left_2
          simp_all only
          use w
          simp_all only [Equiv.toFun_as_coe, and_true]
          have left_2 := left_2
          simp_all only
          rw [Finset.image]
          simp only [Multiset.toFinset_map]
          simp_all only [Finset.val_toFinset]
          rw [Finset.image]
          simp only [Multiset.toFinset_map]
          simp_all only [Finset.val_toFinset]
          convert left
          simp_all only [ge_iff_le, iff_true, n]
          simp only [Finset.image]
          simp_rw [Multiset.toFinset_map]
          simp_all only [Finset.val_toFinset]
          rw [Finset.image]
          rw [Multiset.toFinset_map]
          simp_all only [Finset.val_toFinset]
          convert left_2
          funext x
          ext z
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Finset.mem_map,
            Function.Embedding.coe_subtype]

      have hFG2: ∀ (T : Finset (Fin n)), T ∈ GSet ↔ ∃ S ∈ FSet2, T = Finset.image embedding S:= by
        dsimp [FSet2, projectFSetToGround]
        dsimp[projectToGround]
        dsimp [FSet,GSet]
        simp
        -- goal: ∀ (T : Finset (Fin n)),  T ⊆ (toIdealFinFamily F n hn).ground ∧ (toIdealFinFamily F n hn).sets T ↔ ∃ a, (a ⊆ F.ground ∧ F.sets a) ∧ T = Finset.image embedding (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ a) F.ground.attach)
        intro T
        simp_all only [toIdealFinFamily, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton]
        simp_all only [Equiv.toFun_as_coe, n, embedding]
        obtain ⟨left, right⟩ := pall
        simp_all only [ge_iff_le, n]
        apply Iff.intro
        · intro a
          let ⟨S, hS⟩ := a
          obtain ⟨h1, h2⟩ := hS
          cases h2
          simp_all only [Equiv.toFun_as_coe]
          --goal ∃ S_1,  F.sets (Finset.map (Function.Embedding.subtype fun x => x ∈ F.ground) S_1) ∧ Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S_1
          rename_i right_1
          subst right_1
          obtain ⟨left_2, right_1⟩ := a
          obtain ⟨w, h⟩ := right_1
          obtain ⟨left_3, right_1⟩ := h
          simp_all only
          -- goal ∃ a,  (a ⊆ F.ground ∧ F.sets a) ∧Finset.image (⇑(Fintype.equivFinOfCardEq hn)) w =Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ a) F.ground.attach)
          use w.map (Function.Embedding.subtype _)
          simp_all only [and_true, Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right,
            exists_eq_right]
          apply And.intro
          · intro x hx
            simp_all only [Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right,
              exists_eq_right]
            obtain ⟨w_1, h⟩ := hx
            simp_all only
          · ext1 a
            simp_all only [Finset.mem_image, Subtype.exists, Finset.mem_filter, Finset.mem_attach, true_and,
              Subtype.mk.injEq, exists_prop, exists_and_left]
            apply Iff.intro
            · intro a_1
              obtain ⟨w_1, h⟩ := a_1
              obtain ⟨w_2, h⟩ := h
              obtain ⟨left_4, right_2⟩ := h
              subst right_2
              simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop, exists_eq_right_right,
                and_true]
              apply Exists.intro
              · apply And.intro
                · apply And.intro
                  on_goal 2 => {rfl
                  }
                  · simp_all only
                · simp_all only [exists_const]
            · intro a_1
              obtain ⟨w_1, h⟩ := a_1
              obtain ⟨left_4, right_2⟩ := h
              obtain ⟨w_2, h⟩ := left_4
              obtain ⟨w_3, h_1⟩ := right_2
              obtain ⟨left_4, right_2⟩ := h
              obtain ⟨left_4, right_3⟩ := left_4
              obtain ⟨w_4, h⟩ := right_2
              subst right_3 h_1
              simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_and_right, exists_eq_right,
                exists_const]
        · --(∃ a,    (a ⊆ F.ground ∧ F.sets a) ∧ T =Finset.image (⇑(Fintype.equivFinOfCardEq hn))(Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ a) F.ground.attach)) → T ⊆ (F.toFinFamily F.ground.card hn).ground ∧ ∃ S, F.sets (Finset.map (Function.Embedding.subtype fun x => x ∈ F.ground) S) ∧ T = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S
          --simp_all
          intro a
          obtain ⟨w, ha⟩ := a
          --goal { val := w, nodup := h } ⊆ F.ground → F.sets { val := w, nodup := h } → T = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ { val := w, nodup := h }) F.ground.attach) → Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ { val := w, nodup := h }) F.ground.attach) ⊆ (F.toFinFamily F.ground.card hn).ground ∧ ∃ S, F.sets (Finset.map (Function.Embedding.subtype fun x => x ∈ F.ground) S) ∧ Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ { val := w, nodup := h }) F.ground.attach) = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S
          simp_all
          --intro b
          --intro c
          --intro d
          constructor
          · --subst d
            intro e
            simp_all
            intro f
            intro g
            intro hh
            intro i
            subst i
            --goal  (Fintype.equivFinOfCardEq hn) ⟨f, ⋯⟩ ∈ (F.toFinFamily F.ground.card hn).ground
            --#check Fintype.equivFinOfCardEq hn  -- { x // x ∈ F.ground } ≃ Fin n
            --#check (Fintype.equivFinOfCardEq hn) ⟨f, _⟩
            have univ_eq:(F.toFinFamily F.ground.card hn).ground = Finset.univ:= by
              have hn3: (F.toFinFamily F.ground.card hn).ground.card = Fintype.card (Fin F.ground.card) := by
                simp_all only [Fintype.card_fin]
              exact (Finset.card_eq_iff_eq_univ (F.toFinFamily F.ground.card hn).ground).mp hn3
            simp_all only [Finset.card_univ, Fintype.card_fin, Finset.mem_univ]
          · --goal ∃ S, F.sets (Finset.map (Function.Embedding.subtype fun x => x ∈ F.ground) S)
            -- ∧ Finset.image (⇑(Fintype.equivFinOfCardEq hn))  (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ w) F.ground.attach) = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S
            --expected Finset { x // x ∈ F.ground } -- w : Multiset alpha ha : w.Nodup
            have ha: w ⊆ F.ground := by  --使ってない。
              intro x
              intro hx
              obtain ⟨left_1, right_1⟩ := ha
              obtain ⟨left_1, right_2⟩ := left_1
              subst right_1
              exact left_1 hx
            use F.ground.attach.filter (fun x => x.1 ∈ w)
            rename_i ha_1
            simp_all only [true_and]
            obtain ⟨left_1, right_1⟩ := ha_1
            subst right_1
            apply And.intro
            · --goal F.sets (Finset.map (Function.Embedding.subtype fun x => x ∈ F.ground) (Finset.filter (fun x => ↑x ∈ w) F.ground.attach))
             --#check F.sets
              let S := Finset.map (Function.Embedding.subtype (λ x => x ∈ F.ground)) (Finset.filter (λ x=> ↑x ∈ w) F.ground.attach)
              -- `S` は `w` の部分集合として表されることを確認する
              have hS : S ⊆ w := by
                intro x hx
                simp_all only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
                  Function.Embedding.coe_subtype, Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right,
                  S]
              by_cases hc : S = F.ground
              case pos =>
                -- `S = F.ground` の場合
                simp_all only [S]
                convert left_1
                exact hS.antisymm ha
              case neg =>
               -- `S ≠ F.ground` の場合
                have hS : S ⊆ w := by
                  intro x hx
                  simp_all only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
                    Function.Embedding.coe_subtype, Subtype.exists, exists_and_left, exists_prop,
                    exists_eq_right_right, S]
                -- down_closed の性質を適用
                simp_all only [S]
                convert left_1
                ext1 a
                simp_all only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
                  Function.Embedding.coe_subtype, Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right,
                  and_iff_left_iff_imp]
                intro a_1
                exact ha a_1

            · --goal Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ w) F.ground.attach) = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun x => ↑x ∈ w) F.ground.attach)
              ext1 a
              simp_all only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
                Subtype.mk.injEq, exists_prop, exists_and_left]
              apply Iff.intro
              · intro a_1
                obtain ⟨w_1, h⟩ := a_1
                obtain ⟨left_2, right_1⟩ := h
                obtain ⟨w_2, h⟩ := left_2
                obtain ⟨w_3, h_1⟩ := right_1
                obtain ⟨left_2, right_1⟩ := h
                obtain ⟨left_2, right_2⟩ := left_2
                subst h_1 right_2
                simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop, exists_eq_right_right,
                  and_self]
              · intro a_1
                obtain ⟨w_1, h⟩ := a_1
                obtain ⟨left_2, right_1⟩ := h
                obtain ⟨w_2, h⟩ := right_1
                subst h
                simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop, exists_eq_right_right,
                  and_true]
                use w_1

      have FG_eq: FSet2.card = GSet.card:= by
        apply same_cardinality FSet2 GSet embedding hf hFG2

      dsimp [FSet2, GSet] at FG_eq
      dsimp [projectFSetToGround] at FG_eq
      dsimp [projectToGround] at FG_eq
      dsimp [number_of_hyperedges, normalized_degree_sum]
      symm
      rw [←FG_eq]
      dsimp [FSet]

      -- 写像 i の定義
      let i := λ (s : Finset α) (hs : s ∈ Finset.filter F.sets F.ground.powerset) =>
          Finset.filter (λ y => ∃ x, ∃ (hx: x ∈ F.ground), ⟨x, hx⟩ = y ∧ x ∈ s) F.ground.attach

      -- 写像 i が定義域から値域に写ることの証明
      have hi : ∀ (s : Finset α) (hs : s ∈ Finset.filter F.sets F.ground.powerset),
        i s hs ∈ Finset.image (λ t => Finset.filter (λ y => ∃ x, ∃ (hx : x ∈ F.ground), ⟨x, hx⟩ = y ∧ x ∈ t) F.ground.attach) (Finset.filter F.sets F.ground.powerset) :=
        by
          intros s hs
          apply Finset.mem_image_of_mem
          exact hs

      -- 単射性の証明
      have inj : ∀ (a₁ : Finset α) (ha₁ : a₁ ∈ Finset.filter F.sets F.ground.powerset) (a₂ : Finset α)
    (ha₂ : a₂ ∈ Finset.filter F.sets F.ground.powerset), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂  := by
    --∀ (a₁ a₂ : Finset α) (ha₁ : a₁ ∈ Finset.filter F.sets F.ground.powerset)
    --     (ha₂ : a₂ ∈ Finset.filter F.sets F.ground.powerset), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ := by
        intros a1 ha1 a2 ha2 h_eq

        -- Finset の等式を示すために Finset.ext を適用
        apply Finset.ext

        -- 任意の要素 x に対して、a1 に含まれる ↔ a2 に含まれることを示す
        intro x
        constructor

        -- a1 ⊆ a2 を示す部分
        · -- x ∈ a1 と仮定
          intro h_a1

          -- i a1 ha1 に ⟨x, hx⟩ が含まれることを導く
          have ground_lem:F.ground ∈ Finset.filter F.sets F.ground.powerset := by
            simp_all only [Finset.mem_filter, Finset.mem_powerset]
            constructor
            trivial
            exact F.has_ground

          have x_in_ground: x ∈ F.ground := by
            simp_all only [Equiv.toFun_as_coe, Finset.mem_filter, Finset.mem_powerset, exists_and_right,
              Finset.univ_eq_attach, Finset.mem_image, exists_exists_and_eq_and, and_imp, n, embedding, GSet, FSet2,
              projectFSetToGround, projectToGround, FSet, i]
            simp_all only [Finset.mem_filter, Finset.mem_powerset]
            obtain ⟨left, right⟩ := pall
            obtain ⟨left_1, right_1⟩ := ha1
            obtain ⟨left_2, right_2⟩ := ha2
            simp_all only [ge_iff_le, n]
            apply left_1
            simp_all only

          have y_in_i_a1 : ⟨x, x_in_ground⟩  ∈ i a1 ha1 := by
            dsimp [i]
            simp only [Finset.mem_filter]
            constructor
            simp_all only [Equiv.toFun_as_coe, Finset.mem_filter, Finset.mem_powerset, exists_and_right,
              Finset.univ_eq_attach, Finset.mem_image, exists_exists_and_eq_and, and_imp, subset_refl, true_and,
              Finset.mem_attach, n, embedding, GSet, FSet2, projectFSetToGround, projectToGround, FSet, i]
            use x
            use x_in_ground

          -- i a1 ha1 = i a2 ha2 より、i a2 ha2 にも含まれる
          have y_in_i_a2 : ⟨x, x_in_ground⟩ ∈ i a2 ha2 :=
            h_eq ▸ y_in_i_a1

    -- i a2 ha2 に含まれることから x ∈ a2 を導く
          simp_all only [Equiv.toFun_as_coe, Finset.mem_filter, Finset.mem_powerset, exists_and_right,
            Finset.univ_eq_attach, Finset.mem_image, exists_exists_and_eq_and, and_imp, subset_refl, true_and,
            Finset.mem_attach, Subtype.mk.injEq, exists_prop, and_self, n, embedding, GSet, FSet2,
            projectFSetToGround, projectToGround, FSet, i]
          simp_all only [Finset.mem_filter, Finset.mem_powerset]
          obtain ⟨left, right⟩ := pall
          obtain ⟨left_1, right_1⟩ := ha1
          obtain ⟨left_2, right_2⟩ := ha2
          obtain ⟨w, h_1⟩ := y_in_i_a1
          obtain ⟨left_3, right_3⟩ := h_1
          obtain ⟨left_3, right_4⟩ := left_3
          subst right_4
          simp_all only [ge_iff_le, n]


    -- a2 ⊆ a1 を示す部分
        · -- x ∈ a2 と仮定
          intro h_a2

          -- i a2 ha2 に ⟨x, hx⟩ が含まれることを導く
          have x_in_ground: x ∈ F.ground := by
            simp_all only [Equiv.toFun_as_coe, Finset.mem_filter, Finset.mem_powerset, exists_and_right,
              Finset.univ_eq_attach, Finset.mem_image, exists_exists_and_eq_and, and_imp, n, embedding, GSet, FSet2,
              projectFSetToGround, projectToGround, FSet, i]
            simp_all only [Finset.mem_filter, Finset.mem_powerset]
            obtain ⟨left, right⟩ := pall
            obtain ⟨left_1, right_1⟩ := ha1
            obtain ⟨left_2, right_2⟩ := ha2
            simp_all only [ge_iff_le, n]
            apply left_2
            simp_all only
          have y_in_i_a2 : ⟨x, x_in_ground⟩ ∈ i a2 ha2 := by
            dsimp [i]
            simp only [Finset.mem_filter]
            constructor
            simp_all only [Equiv.toFun_as_coe, Finset.mem_filter, Finset.mem_powerset, exists_and_right,
              Finset.univ_eq_attach, Finset.mem_image, exists_exists_and_eq_and, and_imp, subset_refl, true_and,
              Finset.mem_attach, n, embedding, GSet, FSet2, projectFSetToGround, projectToGround, FSet, i]
            use x
            use x_in_ground
          have y_in_i_a1 : ⟨x, x_in_ground⟩ ∈ i a1 ha1 := by
            simp_all only [Equiv.toFun_as_coe, Finset.mem_filter, Finset.mem_powerset, exists_and_right,
              Finset.univ_eq_attach, Finset.mem_image, exists_exists_and_eq_and, and_imp, Finset.mem_attach,
              Subtype.mk.injEq, exists_prop, true_and, and_self, n, embedding, GSet, FSet2, projectFSetToGround,
              projectToGround, FSet, i]


          -- i a1 ha1 に含まれることから x ∈ a1 を導く

          dsimp [i] at y_in_i_a1
          rw [Finset.mem_filter] at y_in_i_a1
          simp at y_in_i_a1
          exact y_in_i_a1.2

      -- 全射性の証明
      have suj : ∀ (b : Finset { x // x ∈ F.ground }) (hb : b ∈ Finset.image
        (λ s => Finset.filter (λ y => ∃ x, ∃ (hx : x ∈ F.ground), ⟨x, hx⟩ = y ∧ x ∈ s) F.ground.attach)
          (Finset.filter F.sets F.ground.powerset)),
        ∃ a, ∃ (ha: a ∈ Finset.filter F.sets F.ground.powerset), i a ha = b :=
        by
          intros b hb
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
          exact ⟨a, ha, rfl⟩

      -- card_bij の適用
      exact Finset.card_bij i hi inj suj

  case neg =>
    -- n < 2 の場合は、normalized_degree_sum F.toSetFamily <= 0 が自明
    simp_all only [normalized_degree_sum]
    exact Nat.zero_le 0
  have h := P_all 2 (by decide)
  exact h (toIdealFinFamily F 2 (by decide))

end Ideal
