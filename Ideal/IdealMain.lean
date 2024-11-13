--Ideal集合族が平均abundantにならないことの証明。ideal集合族が平均rareであるというメイン定理の型がFin nの場合。
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

variable {α : Type} [DecidableEq α] [Fintype α]

--メイン定理の帰納法のベースケース。大きさ2の場合の証明。
theorem basecase : P 2 := by
  constructor
  simp_all only [ge_iff_le]
  simp_all only [le_refl]
  intros F ground_card
  dsimp [normalized_degree_sum]
  simp_all only [ge_iff_le, zero_add]
  dsimp [total_size_of_hyperedges]
  dsimp [number_of_hyperedges]
  have gr: F.ground = {0, 1} := by
    simp_all only [Fin.isValue]
    have or2: ∀ (a:Fin 2), a = 0 ∨ a = 1 := by
      intro a
      cases a
      --simp_all only [Fin.isValue]
      omega
    apply Finset.eq_of_subset_of_card_le
    --simp_all only [Fin.isValue]
    intro a
    intro _
    simp_all only [Finset.mem_insert, Finset.mem_singleton]--
    simp_all only [Finset.mem_singleton, zero_ne_one, not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, le_refl]--
  rw [gr]
  simp

  have hasground: F.sets {0, 1}:= by
    rw [←gr]
    exact F.has_ground
  have hasempty: F.sets ∅ := by
    exact F.has_empty
  have pow: (Finset.univ : Finset (Fin 2)).powerset = {{0,1}, {0}, {1}, ∅} := by
    simp_all only [Finset.powerset_univ]
    decide
  let zeroone : Finset (Fin 2) := {0, 1}
  have pow2: zeroone.powerset = {{0,1}, {0}, {1}, ∅} := by
    exact pow
  let zp :=  zeroone.powerset
  rw [pow2]

  have zeroonedisj: Disjoint ({zeroone, ∅} : Finset (Finset (Fin 2))) ({{0}, {1}} : Finset (Finset (Fin 2))) := by
    simp_all only [ Finset.disjoint_iff_inter_eq_empty, zeroone]
    decide

  have zeroonedisj2: Disjoint ({0} : (Finset (Fin 2))) ({1} :  (Finset (Fin 2))) := by
    simp_all only [Finset.disjoint_iff_inter_eq_empty, zeroone]
    decide

  have zeroonedisj3: Disjoint (Finset.filter (fun x => F.sets {x}) {0}) (Finset.filter (fun x => F.sets {x}) {1}) := by
    simp_all only [Finset.disjoint_insert_right, one_ne_zero]
    rw [Finset.disjoint_left]
    intro a a_1
    rw [Finset.mem_filter]
    rw [Finset.mem_singleton]
    rw [Finset.mem_filter,Finset.mem_singleton] at a_1
    simp_all only [zero_ne_one, false_and, not_false_eq_true]--

  have zeroonedisj4: Disjoint ({0, 1}:(Finset (Fin 2))) ∅ := by
    simp_all only [Finset.disjoint_empty_right, zeroone]--

  have zeroonedisj5: Disjoint ({{0, 1}}:Finset (Finset (Fin 2))) {∅} := by
    simp_all only [Finset.disjoint_insert_right,or_false, Finset.disjoint_singleton_right, zeroone]
    obtain ⟨left, right⟩ := zeroonedisj
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [Finset.mem_singleton]
    contradiction

  have zerooneunion: ({{0, 1}, ∅} : Finset (Finset (Fin 2))) ∪ ({{0}, {1}} : Finset (Finset (Fin 2))) = {{0, 1}, {0}, {1}, ∅} := by
    decide

  have zerooneunion2: ({0} : Finset (Fin 2)) ∪ ({1} : Finset (Fin 2)) = {0, 1} := by
    decide

  have zerooneunion3: ({{0, 1}, ∅} : Finset (Finset (Fin 2))) = {{0, 1}} ∪  {∅} := by
    rfl

  have leftside: ∑ x in Finset.filter F.sets (Finset.powerset zeroone), x.card = 2 + (Finset.card (Finset.filter (λ x => F.sets {x}) zeroone)) := by
    rw [pow2]
    let dist:= filter_union_distrib F.sets ({{0,1},∅}) ({{0},{1}})
    simp at dist

    let distsum := filter_union_sum F.sets ({{0,1},∅}) ({{0},{1}}) zeroonedisj
    let filtereq := filter_union_eq F.sets ({{0,1},∅}) ({{0},{1}})
    simp at filtereq
    rw [zerooneunion] at distsum
    rw [←distsum]

    have goal1:  ∑ x ∈ Finset.filter F.sets {{0, 1}, ∅}, x.card = 2 := by
      simp_all only [  zeroone, zp]
      simp_all only [Finset.disjoint_insert_right]
      simp [Finset.filter_true_of_mem, *]
      rfl

    have goal2: ∑ x ∈ Finset.filter F.sets {{0}, {1}}, x.card = (Finset.filter (fun x => F.sets {x}) zeroone).card := by
      rw [Finset.sum_filter, Finset.card_filter]
      simp
      dsimp [zeroone]
      --simp_all only [Fin.isValue]
      let result0 := filter_union_eq0 (fun x => F.sets {x}) {0} {1}

      rw [zerooneunion2] at result0
      rw [result0]
      have term1: (if F.sets {0} then 1 else 0) = (Finset.filter (fun x => F.sets {x}) {0}).card := by
        simp
        by_cases h01: F.sets {0}
        · case pos =>
          simp_all only [↓reduceIte, zeroone]

          symm
          simp [result0, Finset.filter_singleton]
          simp_all only [↓reduceIte, Finset.card_singleton]
        · case neg =>
          simp_all only [ ↓reduceIte, zeroone]
          symm
          simp_all only [ Finset.card_eq_zero]
          ext1 a
          rw [Finset.mem_filter]
          rw [Finset.mem_singleton]
          simp_all only [Finset.not_mem_empty, iff_false,not_and, not_false_eq_true, implies_true]--

      have term2: (if F.sets {1} then 1 else 0) = (Finset.filter (fun x => F.sets {x}) {1}).card := by
        simp
        by_cases h10: F.sets {1}
        · case pos =>
          simp_all only [ ↓reduceIte, zeroone]
          symm
          simp [result0, Finset.filter_singleton]
          simp_all only [↓reduceIte, Finset.card_singleton]
        · case neg =>
          simp_all only [ ↓reduceIte]--
          symm
          simp_all only [Finset.card_eq_zero]--
          ext1 a
          rw [Finset.mem_filter,Finset.mem_singleton]
          simp_all only [Finset.not_mem_empty,  iff_false,not_and, not_false_eq_true, implies_true]--

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

    simp_all only [Finset.insert_union]

  rw [pow2] at leftside
  --rw [leftside] 表面上一致しているが、一致しない。
  have rightside: (Finset.filter F.sets zeroone.powerset).card =  2 + (Finset.card (Finset.filter (λ s => F.sets s) {{0},{1}})) := by
    have rightside_lem: (Finset.filter F.sets zeroone.powerset).card = (Finset.card (Finset.filter (λ s => F.sets s) {zeroone, ∅})) + (Finset.card (Finset.filter (λ s => F.sets s) {{0},{1}})) := by
      rw [pow2]
      rw [←zerooneunion]
      --lemma filter_union_eq (P : Finset α → Prop) [DecidablePred P] (A B : Finset (Finset α)) : (A ∪ B).filter P = (A.filter P) ∪ (B.filter P)
      rw [filter_union_eq F.sets {{0, 1}, ∅} {{0}, {1}}]
      simp_all only [Finset.disjoint_insert_right, zeroone]
      obtain ⟨left, right⟩ := zeroonedisj
      rw [Finset.card_union_of_disjoint]
      symm
      apply Finset.disjoint_filter_filter
      simp_all only [  Finset.mem_singleton, or_false, Finset.disjoint_union_right, Finset.disjoint_singleton_right,Finset.mem_insert, Finset.insert_eq_self, zero_ne_one, not_or]--
      apply And.intro
      · apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [ Finset.mem_singleton,Finset.singleton_ne_empty, or_false, Finset.mem_union, Finset.subset_singleton_iff, Finset.union_eq_left]--
      · apply And.intro
        · apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [ Finset.singleton_inj, zero_ne_one, Finset.mem_singleton, or_true, Finset.insert_eq_of_mem, Finset.mem_union]
          contradiction
        · apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.union_idempotent]
          contradiction

    have rightside_eq2:(Finset.card (Finset.filter (λ s => F.sets s) {zeroone, ∅})) = 2:= by
      dsimp [zeroone]
      rw [zerooneunion3]
      rw [filter_union_eq F.sets {{0, 1}} {∅}]

      have disjoint_filtered := (@Finset.disjoint_filter_filter _ ({{0, 1}}:Finset (Finset (Fin 2))) {∅} F.sets F.sets) zeroonedisj5
      rw [Finset.card_union_of_disjoint disjoint_filtered]
      simp
      have value2: (Finset.filter F.sets {{0, 1}}).card = 1 := by
        have assum: ∀ x∈ ({{0,1}}:Finset (Finset (Fin 2))), F.sets x := by
          intro x
          --simp_all only [Fin.isValue]
          obtain ⟨val, property⟩ := x
          intro a
          simp_all only [Finset.mem_singleton]
        rw [(Finset.filter_eq_self).mpr assum]
        simp_all only [ Finset.mem_singleton, forall_eq, Finset.card_singleton]

      have value0: (Finset.filter F.sets {∅}).card = 1:= by
        --hasempty : F.sets ∅
        have assum: ∀ x∈ ({∅}:Finset (Finset (Fin 2))), F.sets x := by
          intro x
          simp_all only [Fin.isValue]
          obtain ⟨val, property⟩ := x
          intro a
          simp_all only [Finset.mem_singleton]
        rw [(Finset.filter_eq_self).mpr assum]
        simp only [Finset.card_singleton]

      omega

    rw [rightside_lem]
    rw [rightside_eq2]

  simp_all only [zeroone]
  norm_cast
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
      simp_all only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.singleton_inj,  i, range]--
      simp_all only [Finset.mem_insert, Finset.mem_filter,  Finset.mem_singleton, and_self, domain]--
    have inj: ∀ (a₁ : Fin 2) (ha₁ : a₁ ∈ domain) (a₂ : Fin 2) (ha₂ : a₂ ∈ domain), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ := by
      intro a₁ ha₁ a₂ ha₂ a
      simp_all only [ Finset.singleton_inj,domain, i]
    have surj: ∀ s ∈ range, ∃ (x : Fin 2), ∃ (h : x ∈ domain), i x h = s := by
      intro s a
      simp_all only [ Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,exists_prop, domain, i, range]--
      obtain ⟨left_1, right_1⟩ := a
      cases left_1 with
      | inl h =>
        subst h
        simp_all only [Finset.singleton_inj, exists_eq_right, zero_ne_one, or_false, and_self]--
      | inr h_1 =>
        subst h_1
        simp_all only [Finset.singleton_inj, exists_eq_right, one_ne_zero, or_true, and_self]


    let cardbij := @Finset.card_bij _ _ domain range i hi inj surj
    rw [cardbij]
  rw [new_goal]

  --leftsideとrightsideを使って、goalを証明する。
theorem inductive_step {n:Nat} (n_ge_two: n >= 2) (h_ind: P n) : P (n+1) := by

  have n_ge_one : n ≥ 1 := by omega
  unfold P at h_ind ⊢
  obtain ⟨n_ge_two, h_ind⟩ := h_ind

  constructor
  simp_all only [ge_iff_le, Nat.reduceLeDiff]
  intros F ground_card
   -- n ≥ 2 から n + 1 ≥ 3 を導く
  have ground_ge_two: F.ground.card >= 2 := by
    have h1 : n + 1 ≥ 3 := Nat.succ_le_succ n_ge_two
    -- F.ground.card = n + 1 なので、F.ground.card ≥ 3
    rw [←ground_card] at h1
    -- F.ground.card ≥ 3 なので F.ground.card ≥ 2 も成立
    exact Nat.le_of_succ_le h1

  obtain ⟨v, hv⟩ := ideal_version_of_frankl_conjecture F
  obtain ⟨v_in_ground, hv_right⟩ := hv

  by_cases singleton_hyperedge_have: F.sets {v}
  · case pos =>

    set Fdel := idealdeletion F v v_in_ground ground_ge_two
    have Fvx: v ∉ Fdel.ground := by
      intro h
      simp_all only [ge_iff_le]
      dsimp [Fdel] at h
      dsimp [idealdeletion] at h
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false]--

    have ground_Fdel_card: Fdel.ground.card = n := by
      simp_all only [ge_iff_le]
      simp_all only [Fdel]
      rw [idealdeletion]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]

    have ground_delF_card_ge_one: Fdel.ground.card ≥ 1 := by
      simp_all only [ge_iff_le]

    --#check IdealFamily.deletionToN n_ge_one Fdel v Fvx ground_delF_card_ge_one
    set h_idealdeletion := IdealFamily.deletionToN n_ge_one Fdel v Fvx ground_delF_card_ge_one

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
      simp_all only [Fcont]
      rw [contraction_ideal_family]
      simp_all only [add_tsub_cancel_right]
      rw [contraction]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]--

    have h_cont2: Fcont.ground.card ≥ 1 := by
      simp_all only [ge_iff_le]

    have Fvx2: v ∉ Fcont.ground := by
      intro h
      simp_all only [ge_iff_le]
      dsimp [Fcont] at h
      simp_all only [Fcont]
      dsimp [contraction_ideal_family] at h
      dsimp [contraction] at h
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false]--

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

    set total_del := total_size_of_hyperedges (idealdeletion F v v_in_ground ground_ge_two).1
    set number_del := (number_of_hyperedges (idealdeletion F v v_in_ground ground_ge_two).1)
    set total_cont := total_size_of_hyperedges (contraction_ideal_family F v singleton_hyperedge_have ground_ge_two).toSetFamily
    set number_cont := (number_of_hyperedges (contraction_ideal_family F v singleton_hyperedge_have ground_ge_two).toSetFamily)
    set total := (total_size_of_hyperedges F.toSetFamily)
    set  number := (number_of_hyperedges F.toSetFamily)
    set degreev := (degree F.toSetFamily v)

    classical
    by_cases hv_hyperedge:(F.sets (F.ground \ {v}))
    ·   case pos =>
        have h_sum_have := (hyperedge_average_have F v v_in_ground ground_ge_two) hv_hyperedge singleton_hyperedge_have
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
        simp_all only [tsub_le_iff_right, zero_add, Nat.cast_add,  degreev, number, h_idealdeletion,
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

end Ideal
