--Ideal集合族が平均abundantにならないことの証明が目標。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import Ideal.IdealDeletion
import Ideal.IdealSumBasic
import Ideal.IdealNumbers
import LeanCopilot
--set_option maxHeartbeats 1000000

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α]

def ff (s: Finset α): ℕ := Finset.card s - 1

--omit [Nonempty α] in
lemma contraction_family_size (F : SetFamily α) [DecidablePred F.sets] (x : α)
  (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2) : total_size_of_hyperedges (contraction F x hx ground_ge_two) = (Finset.filter (fun s ↦ ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset).sum Finset.card :=
  by
    rw [total_size_of_hyperedges]
    dsimp [contraction]
    rw [Finset.filter_congr_decidable]

--omit [Nonempty α] in
lemma contraction_total_size (F : SetFamily α) [DecidablePred F.sets] (x : α)
  (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2) :
  total_size_of_hyperedges (contraction F x hx ground_ge_two) =
    ((Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)).sum (λ s => Finset.card s - 1) :=
  by
    rw [total_size_of_hyperedges]
    let largeset:= Finset.filter (fun s ↦ F.sets s ∧ x ∈ s) F.ground.powerset
    --have largesethave: largeset = Finset.filter (fun s ↦ F.sets s ∧ x ∈ s) F.ground.powerset := by rfl
    let smallset:= Finset.filter (fun s ↦ ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset
    --have smallsethave: smallset = Finset.filter (fun s ↦ ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset := by rfl
    have sum_eq0 := sum_of_size_eq_degree_plus_contraction_sum F x ground_ge_two
    have sum_eq2 := sumbij F x hx
    simp_all

    have substitute1: (Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum (λ s => Finset.card s - 1) = largeset.sum (λ s => Finset.card s - 1) := by rfl
    have substitute2: (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum Finset.card = smallset.sum Finset.card := by rfl
    rw [←substitute1]
    have sum_eq3 : ∑ s ∈ largeset, (s.card - 1) = largeset.sum (λ s => s.card - 1) := by rfl
    rw [←sum_eq3]

    have f_eq : ∀ s ∈ largeset, ff s = Finset.card s - 1 := by
        intros s _
        simp only [ff]

    have sum_eq3: largeset.sum (λ s => s.card - 1) = largeset.sum ff := by rfl
    have sum_eq5: largeset.sum (ff) + largeset.card = largeset.sum (λ s => ff s + 1) := by
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_const]
      simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, Finset.one_le_card, and_imp, Pi.sub_apply,
        Pi.one_apply, smul_eq_mul, mul_one, smallset, largeset]

    let contset := (Finset.filter (contraction F x hx ground_ge_two).sets (contraction F x hx ground_ge_two).ground.powerset)
    have contsethave: contset = (Finset.filter (contraction F x hx ground_ge_two).sets (contraction F x hx ground_ge_two).ground.powerset) := by rfl
    rw [←contsethave]

    have substitute3: (Finset.filter (contraction F x hx ground_ge_two).sets (contraction F x hx ground_ge_two).ground.powerset).sum Finset.card = contset.sum Finset.card := by rfl
    rw [substitute3]
    have sum_eq4 : ∑ s ∈ largeset, (s.card - 1) = largeset.sum (λ s => s.card - 1) := by rfl
    rw [←sum_eq4]
    rw [sum_eq3]
    rw [substitute2] at sum_eq0
    rw [substitute2] at sum_eq0
    have substitute4: (Finset.filter (fun s ↦ ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset).card  = smallset.card := by rfl
    rw [substitute4] at sum_eq0
    --#check sum_eq0 --smallset.sum Finset.card + smallset.card = degree F x + smallset.sum Finset.card

    let sumbijlocal := sumbij F x hx
    -- let domain00 := Finset.filter (fun s ↦ F.sets s ∧ x ∈ s) F.ground.powerset;
    have sumbijihave :largeset.sum Finset.card = smallset.sum Finset.card + smallset.card := sumbij F x hx

    let contsizelocal := contraction_family_size F x hx ground_ge_two
    dsimp [total_size_of_hyperedges] at contsizelocal
    rw [substitute3] at contsizelocal
    rw [substitute2] at contsizelocal
    rw [contsizelocal]
    --goal  smallset.sum Finset.card = largeset.sum ff
    --sumbijhave: largeset.sum Finset.card = smallset.sum Finset.card + smallset.card
    --goalは、sumbijhaveを移項したもの。よって、あとは、largeset.sum Finset.card 　>=  smallset.cardがわかればよい。

    have positive: ∀ s ∈ largeset, s.card ≥ 1 := by
      intros s hs
      simp only [Finset.mem_filter] at hs
      rename_i inst _ _ _
      simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, Finset.one_le_card, smallset, largeset]
      obtain ⟨_, right⟩ := hs
      obtain ⟨_, right⟩ := right
      exact ⟨x, right⟩

    have largesum_lt_smallcard: largeset.sum Finset.card >= largeset.card := by
      have largesum_ge_1: ∀ s ∈ largeset, s.card >= 1 := by
        intros s hs
        simp only [Finset.mem_filter] at hs
        exact positive s hs
      calc
        largeset.sum Finset.card = largeset.sum (λ s=> s.card) := by simp
        _ >= largeset.sum (λ s => 1) := Finset.sum_le_sum largesum_ge_1
        _ = largeset.card * 1 := by
          --rename_i inst inst_1 _ inst_3 _
          simp_all only [Finset.mem_filter, Finset.mem_powerset, ge_iff_le, and_self, and_imp, implies_true,
            Finset.one_le_card, Finset.sum_const, smul_eq_mul, mul_one, smallset, sumbijlocal, largeset, contset]
        _ = largeset.card := by simp

    have largecard_eq_smallcard: largeset.card = smallset.card := by
        dsimp [largeset]
        dsimp [smallset]
        exact (card_equal F x hx)

    rw [largecard_eq_smallcard] at largesum_lt_smallcard
    rw [ge_iff_le] at largesum_lt_smallcard
    --sumbijhave: largeset.sum Finset.card = smallset.sum Finset.card + smallset.card
    --goal: smallset.sum Finset.card = largeset.sum ff = largeset.sum Finset.card - smallset.card

    have calc0 : (largeset.sum Finset.card) - smallset.card = smallset.sum Finset.card := by
      calc
        largeset.sum Finset.card -smallset.card
            = (smallset.sum Finset.card + smallset.card) - smallset.card := by rw [sumbijihave]
          _ = smallset.sum Finset.card  := by rw [Nat.add_sub_cancel]

    rw [←calc0]
    rw [←largecard_eq_smallcard]

    have sum_subst: largeset.sum (λ s => ff s + 1) = largeset.sum Finset.card := by
      dsimp [ff]
      apply Finset.sum_congr rfl
      intro s hs
      -- s.card - 1 + 1 = s.card を示す
      rw [Nat.sub_add_cancel (positive s hs)]

    rw [sum_subst] at sum_eq5
    -- sum_eq5: largeset.sum ff + largeset.card = largeset.sum Finset.card
    -- goal largeset.sum Finset.card - largeset.card = largeset.sum ff
    rw [←sum_eq5]
    --goal largeset.sum ff + largeset.card - largeset.card = largeset.sum ff
    rw [Nat.add_sub_cancel]



--omit [Nonempty α] in
lemma filter_sum_eq (F : SetFamily α) (x : α) (hx : x ∈ F.ground) [DecidablePred F.sets] :
  (Finset.filter (λ s => F.sets s ∧ x ∉ s) F.ground.powerset).sum Finset.card =
  (Finset.filter (λ s => F.sets s ∧ x ∉ s) (F.ground.erase x).powerset).sum Finset.card :=
by

  -- `h1` を用いて、式を簡略化
  apply Finset.sum_congr
  apply Finset.ext
  intro s
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase]
  -- 明示的には以下の補題は使ってないが、裏で役に立っている。
  have lem: x ∉ s → ( s ⊆ F.ground ↔ s ⊆ F.ground.erase x) := by
    intro h
    constructor
    intro a
    intro y
    intro hy
    by_cases h1: y = x
    rw [h1] at hy
    subst h1
    contradiction
    simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
    exact a hy
    intro h2
    exact h2.trans (Finset.erase_subset _ _)

  simp_all only [and_congr_left_iff, not_false_eq_true, and_imp, implies_true]

  intro x_1 _

  simp_all only [Finset.mem_filter, Finset.mem_powerset]

----idealdeletionじゃなくて、deletionで等式を証明して、そこから(hx_hyperedge : F.sets (F.ground \ {x}))かどうかで分岐するのが良いかもしれない。
---F.sets (F.ground \ {x}))が成り立つかどうかでidealdeletionとdeletionの関係を書く。
--ground-vがhyepredgeである場合とない場合の共通の部分の言明。この方法がいいのかわからない。
theorem hyperedge_totalsize_deletion_contraction{α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred F.sets] (singleton_have :F.sets {x}) :
  ((total_size_of_hyperedges F.toSetFamily):ℤ) =
  ((total_size_of_hyperedges (deletion F.toSetFamily x hx ground_ge_two)):ℤ)  +
  ((total_size_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily:ℤ))
  + ((degree F.toSetFamily x):ℤ):=
by
    have sub1 :  total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∈ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } =
    (Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum Finset.card := by
      rfl

    have sub2: total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∉ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } =
    (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
      rfl

    have sub3: (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum Finset.card =
       total_size_of_hyperedges  (contraction F.toSetFamily x hx ground_ge_two) := by
      dsimp [total_size_of_hyperedges]
      dsimp [contraction]
      congr

    have sub4: (Finset.filter (λ s => F.sets s ∧ x  ∉ s) (Finset.powerset F.ground)).sum Finset.card = total_size_of_hyperedges (deletion F.toSetFamily x hx ground_ge_two) := by
      dsimp [total_size_of_hyperedges]
      dsimp [deletion]
      rw [filter_sum_eq]
      congr
      exact hx

    calc
      ((total_size_of_hyperedges F.toSetFamily:ℤ))
          = ((total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∈ s, inc_ground := λ s hs => F.inc_ground s (hs.1) }):ℤ) +
            ((total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∉ s, inc_ground := λ s hs => F.inc_ground s (hs.1) }):ℤ) := by
              rw [←(sum_partition_by_v F.toSetFamily x)]
              simp_all only [Nat.cast_add, Nat.cast_sum]
       _  = (Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum Finset.card +
            (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
              rw [sub1]
              rw [sub2]
       _  = degree F.toSetFamily x + (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum Finset.card +
            (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
              rw [sum_of_size_eq_degree_plus_contraction_sum F.toSetFamily x ground_ge_two]
              simp_all only [Nat.cast_add, Nat.cast_sum]
       _  = degree F.toSetFamily x + total_size_of_hyperedges  (contraction F.toSetFamily x hx ground_ge_two)
               + (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
              rw [sub3]
       _  = degree F.toSetFamily x + total_size_of_hyperedges  (contraction F.toSetFamily x hx ground_ge_two) +
            total_size_of_hyperedges (deletion F.toSetFamily x hx ground_ge_two) := by
              rw [sub4]
       _  = total_size_of_hyperedges (deletion F.toSetFamily x hx ground_ge_two)  +
            total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two) + degree F.toSetFamily x := by
              ring

--後ろのtheorem hyperedge_average_haveで使われている。
theorem hyperedge_totalsize_deletion_contraction_have {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred F.sets] (hx_hyperedge : F.sets (F.ground \ {x})) :
  total_size_of_hyperedges F.toSetFamily =
  total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily  +
  total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two) + degree F.toSetFamily x:=

  by
    --#check sum_partition_by_v F.toSetFamily x
    have sub1 :  total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∈ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } =
    (Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum Finset.card := by
      rfl

    have sub2: total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∉ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } =
    (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
      rfl

    have sub3: (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum Finset.card =
       total_size_of_hyperedges  (contraction F.toSetFamily x hx ground_ge_two) := by
      dsimp [total_size_of_hyperedges]
      dsimp [contraction]
      congr

    have sub4: (Finset.filter (λ s => F.sets s ∧ x  ∉ s) (Finset.powerset F.ground)).sum Finset.card = total_size_of_hyperedges (deletion F.toSetFamily x hx ground_ge_two) := by
      dsimp [total_size_of_hyperedges]
      dsimp [deletion]
      rw [filter_sum_eq]
      congr
      exact hx

    have sub5: (idealdeletion F x hx ground_ge_two).toSetFamily = (deletion F.toSetFamily x hx ground_ge_two) := by
      rw [idealdeletion]
      rw [deletion]
      simp_all
      ext x_1 : 2
      simp_all only [or_iff_left_iff_imp, Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]
      intro a
      subst a
      convert hx_hyperedge
      ext1 a
      simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
      apply Iff.intro
      · intro a_1
        simp_all only [not_false_eq_true, and_self]
      · intro a_1
        simp_all only [not_false_eq_true, and_self]
    calc
      total_size_of_hyperedges F.toSetFamily
          = total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∈ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } +
            total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∉ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } := by
              rw [←(sum_partition_by_v F.toSetFamily x)]
       _  = (Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum Finset.card +
            (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
              rw [sub1]
              rw [sub2]
       _  = degree F.toSetFamily x + (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum Finset.card +
            (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
              rw [sum_of_size_eq_degree_plus_contraction_sum F.toSetFamily x ground_ge_two]
       _  = degree F.toSetFamily x + total_size_of_hyperedges  (contraction F.toSetFamily x hx ground_ge_two)
               + (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
              rw [sub3]
       _  = degree F.toSetFamily x + total_size_of_hyperedges  (contraction F.toSetFamily x hx ground_ge_two) +
            total_size_of_hyperedges (deletion F.toSetFamily x hx ground_ge_two) := by
              rw [sub4]
       _  = degree F.toSetFamily x + total_size_of_hyperedges  (contraction F.toSetFamily x hx ground_ge_two) +
            total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily := by
              rw [←sub5]
       _  = total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily +
            total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two) +(degree F.toSetFamily x):= by
              ring


theorem hyperedge_totalsize_deletion_contraction_have_z {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred F.sets] (hx_hyperedge : F.sets (F.ground \ {x})) :
  ((total_size_of_hyperedges F.toSetFamily):ℤ) =
  ((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ)   +
  ((total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)):ℤ)  + ((degree F.toSetFamily x):ℤ):=
  by
    rw [hyperedge_totalsize_deletion_contraction_have F x hx ground_ge_two hx_hyperedge]
    congr

/-どこからも使われてなさそう。
omit [Fintype α]  in
theorem filter_powerset_sum {A : Finset α} (h : x ∈ A):
  (A.powerset.filter (fun s => s = A.erase x)).sum Finset.card = A.card - 1 :=
  by
    -- フィルタされた部分集合は A.erase x のみを含む
    have h₁ : (A.powerset.filter (fun s => s = A.erase x)) = {A.erase x} := by
      ext s
      simp [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      intro a
      subst a
      intro y hy
      simp_all only [Finset.mem_erase, ne_eq]
    rw [h₁, Finset.sum_singleton]

    exact Finset.card_erase_of_mem h
-/

--後ろで使われている。
lemma disjoint_sum_card_eq {α : Type*} [DecidableEq α] {A B : Finset (Finset α)} (h : A ∩ B = ∅) :
  (A ∪ B).sum Finset.card = A.sum Finset.card + B.sum Finset.card :=
by
  -- `A ∩ B = ∅` という仮定から、A と B が互いに素であることを示す
  have h_disjoint : Disjoint A B := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact h

  -- `sum_union` を使って A ∪ B の和が A と B の和に分かれることを証明
  symm
  rw [Finset.sum_union h_disjoint]

--後ろのideal_and_deletion_zで使われている。
lemma ideal_and_deletion {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2) (ground_v_none : ¬ F.sets (F.ground \ {x})) :
  total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily = total_size_of_hyperedges (deletion F.toSetFamily x hx ground_ge_two) + (F.ground.card - 1):=
  by

    have sub4: (Finset.filter (λ s => F.sets s ∧ x  ∉ s) (Finset.powerset F.ground)).sum Finset.card = total_size_of_hyperedges (deletion F.toSetFamily x hx ground_ge_two) := by
      dsimp [total_size_of_hyperedges]
      dsimp [deletion]
      rw [filter_sum_eq]
      congr
      exact hx

    rw [←sub4]
    rw [total_size_of_hyperedges]
    simp_all
    rw [idealdeletion]
    rw [total_size_of_hyperedges]
    rw [deletion]

    have disj: Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) F.ground.powerset ∩ Finset.filter (fun s ↦ s = F.ground.erase x) F.ground.powerset = ∅ := by
      apply Finset.eq_empty_of_forall_not_mem
      intro a
      simp_all only [Finset.mem_inter, Finset.mem_filter, Finset.mem_powerset]
      intro h
      obtain ⟨h1, h2⟩ := h
      simp_all only [and_self, and_true, not_false_eq_true, and_imp, implies_true, not_true_eq_false]
      let state1 := h1.2.1
      rw [←(Finset.sdiff_singleton_eq_erase x (F.ground))] at state1
      contradiction

    rw [←Finset.disjoint_iff_inter_eq_empty] at disj --Disjointに。

    have sub6:  (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) F.ground.powerset ∪
        Finset.filter (fun s ↦ s = F.ground.erase x) F.ground.powerset).card =
    (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) F.ground.powerset).card +
      (Finset.filter (fun s ↦ s = F.ground.erase x) F.ground.powerset).card := by
        apply (Finset.card_union_of_disjoint disj) --効果なし？

    have sub7: (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) F.ground.powerset ∪
        Finset.filter (fun s ↦ s = F.ground.erase x) F.ground.powerset) =  (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) F.ground.powerset) := by
        apply Finset.ext
        intro a
        simp_all only [Finset.mem_union, Finset.mem_filter, Finset.mem_powerset]
        apply Iff.intro
        intro h
        simp_all only [Finset.card_union_of_disjoint]
        cases h with
        | inl h_1 => simp_all only [not_false_eq_true, and_self, true_or]
        |
          inr h_2 =>
          simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true, or_true]
          obtain ⟨left, right⟩ := h_2
          subst right
          simp_all only
        intro a_1
        simp_all only [Finset.card_union_of_disjoint, true_and]

    have sub8: ((Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) F.ground.powerset ∪ Finset.filter (fun s ↦ s = F.ground.erase x) F.ground.powerset)).sum Finset.card =
     (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) F.ground.powerset).sum Finset.card := by
      rw [sub7]

    have sub9:Finset.filter (λ s=> F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) F.ground.powerset = Finset.filter (λ s=> F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) (F.ground.erase x).powerset
      := by
        apply Finset.ext
        intro ss
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase]
        apply Iff.intro
        intro a
        obtain ⟨left, right⟩ := a
        constructor
        cases right with
        | inl h =>
          --left : ss ⊆ F.groundとright : x ∉ ssから、ss ⊆ F.ground.erase xを示す。
          intro y
          intro hy
          rw [Finset.erase_eq]
          rw [Finset.mem_sdiff]
          constructor
          --goal y ∈ F.ground
          exact left hy
          --goal y ≠ x
          intro hh
          have xy: x = y := by
            rw [Finset.mem_singleton] at hh
            exact hh.symm
          rw [xy]  at h
          let hright:= h.2
          contradiction
        | inr h =>
          subst h
          rfl
        --goal F.sets ss ∧ x ∉ ss ∨ ss = F.ground.erase x
        cases right with
        | inl h =>
          exact Or.inl h
        | inr h =>
          exact Or.inr h
        --多分逆方向
        intro aa
        obtain ⟨left0, right0⟩ := aa
        constructor
        cases right0 with
        | inl h =>
          --left0 : ss ⊆ F.ground.erase xとright0 : x ∉ ssから、ss ⊆ F.groundを示す。
          intro y
          intro hy
          --y ∈ F.ground
          let hy1 := left0 hy
          rw [Finset.erase_eq] at hy1
          rw [Finset.mem_sdiff] at hy1
          exact hy1.1
        | inr h =>
          subst h
          intro y hy
          rw [Finset.mem_erase] at hy
          exact hy.2
        --goal F.sets ss ∧ x ∉ ss ∨ ss = F.ground.erase x
        exact right0

    have sub11: (Finset.filter (fun s => s = F.ground.erase x) F.ground.powerset) = {F.ground.erase x} := by
      apply Finset.ext
      intro s
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      apply Iff.intro
      intro a

      obtain ⟨_, right⟩ := a
      exact right

      intro a
      constructor
      have lem: F.ground.erase x ⊆ F.ground := by
        exact Finset.erase_subset x F.ground
      rw [←a] at lem
      exact lem
      exact a

    have sub10: (Finset.filter (fun s => s = F.ground.erase x) F.ground.powerset).sum Finset.card = (F.ground.card - 1) := by
      rw [sub11]
      simp_all only [Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, ne_eq,
        not_true_eq_false, and_true, not_false_eq_true, not_and, implies_true, Finset.card_union_of_disjoint,
        Finset.card_singleton, Finset.sum_singleton, Finset.card_erase_of_mem]

    set h_lhs := (Finset.filter (λ s=> F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) F.ground.powerset).sum Finset.card with h_lhs_def
    set h_rhs := (Finset.filter (λ s=> F.sets s ∧ x ∉ s) F.ground.powerset).sum Finset.card + (F.ground.card - 1) with h_rhs_def
    set h_rhs0 := (Finset.filter (λ s=> F.sets s ∧ x ∉ s) F.ground.powerset).sum Finset.card with h_rhs0_def
    set h_lhs1 := Finset.filter (λ s=> F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) F.ground.powerset with h_lhs1_def
    set h_rhs1 := Finset.filter (λ s=> F.sets s ∧ x ∉ s) F.ground.powerset with h_rhs1_def

    have sub9': h_lhs1 = Finset.filter (λ s=> F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) (F.ground.erase x).powerset :=
      by
        rw [←sub9]

    have goal1: h_lhs = h_rhs := by --h_rhs_defだとエラーになる。
      dsimp [h_lhs, h_rhs]
      dsimp [h_lhs] at sub8
      rw [←sub8]
      rw [←sub10]

      rw [Finset.disjoint_iff_inter_eq_empty] at disj
      rw [←(disjoint_sum_card_eq disj)]

    simp only [h_lhs_def, h_rhs_def] at goal1
    simp only [h_lhs1_def, h_rhs1_def,h_rhs0] at goal1

    set h_lhs_e := (Finset.filter (λ s=> F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) (F.ground.erase x).powerset).sum Finset.card with h_lhs_def
    set h_rhs_e := (Finset.filter (λ s=> F.sets s ∧ x ∉ s) (F.ground.erase x).powerset).sum Finset.card + (F.ground.card - 1) with h_rhs_def
    set h_rhs0_e := (Finset.filter (λ s=> F.sets s ∧ x ∉ s) (F.ground.erase x).powerset).sum Finset.card  with h_rhs0_e_def

    have goal_e: h_lhs_e = h_rhs_e := by
      dsimp [h_lhs_e, h_rhs_e]
      rw [←sub9]
      rw [goal1]
      rw [←h_rhs0_def]
      rw [←h_rhs_def]
      have sub12: h_rhs0 + (F.ground.card - 1) = h_rhs := by
        dsimp [h_rhs0]
      rw [sub12]
      dsimp [h_rhs, h_rhs_e]
      rw [←h_rhs0_def]
      rw [←h_rhs0_e_def]

      have goale1: (Finset.filter (fun s => F.sets s ∧ x ∉ s) F.ground.powerset) =(Finset.filter (fun s => F.sets s ∧ x ∉ s) (F.ground.erase x).powerset):=
        by
          apply Finset.ext
          intro s
          simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase]
          apply Iff.intro
          intro a
          obtain ⟨left, right⟩ := a
          constructor
          intro y
          intro hy
          simp_all only [Finset.sum_singleton, Finset.card_erase_of_mem, Finset.disjoint_singleton_right,
            Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
            not_false_eq_true, not_and, implies_true, Finset.card_union_of_disjoint, Finset.card_singleton, h_rhs0,
            h_rhs, h_lhs1, h_lhs, h_rhs1, h_lhs_e, h_rhs_e, h_rhs0_e]
          obtain ⟨_, right⟩ := right
          apply And.intro
          · apply Aesop.BuiltinRules.not_intro
            intro a
            subst a
            simp_all only
          · exact left hy
          simp_all only [Finset.sum_singleton, Finset.card_erase_of_mem, Finset.disjoint_singleton_right,
            Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
            not_false_eq_true, not_and, implies_true, Finset.card_union_of_disjoint, Finset.card_singleton, and_self,
            h_rhs0, h_rhs, h_lhs1, h_lhs, h_rhs1, h_lhs_e, h_rhs_e, h_rhs0_e]
          --goal s ⊆ F.ground.erase x ∧ F.sets s ∧ x ∉ s → s ⊆ F.ground ∧ F.sets s ∧ x ∉ s

          intro a
          obtain ⟨left_1, right⟩ := a
          constructor
          · intro y
            intro hy
            simp_all only [Finset.mem_erase, Finset.mem_sdiff]
            have lem: F.ground.erase x ⊆ F.ground := by
              simp_all only [Finset.sum_singleton, Finset.card_erase_of_mem, Finset.disjoint_singleton_right,
                Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
                not_false_eq_true, not_and, Finset.card_singleton, h_rhs, h_rhs0, h_lhs1, h_lhs_e]
              --obtain ⟨left, right⟩ := right
              intro z hz
              simp_all only [Finset.mem_erase, ne_eq]
            have lem2: s  ⊆ F.ground := by
              exact subset_trans left_1 lem
            exact lem2 hy
          · exact right

      have goal_e0: h_rhs0 = h_rhs0_e := by
        dsimp [h_rhs0, h_rhs0_e]
        rw [←goale1]
      rw [←goal_e0]
    simp_all only [Finset.sum_singleton, Finset.card_erase_of_mem, Finset.disjoint_singleton_right, Finset.mem_filter,
      Finset.mem_powerset, Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true, not_and,
      implies_true, Finset.card_union_of_disjoint, Finset.card_singleton, add_left_inj, h_rhs0, h_rhs, h_lhs1, h_lhs,
      h_rhs1, h_lhs_e, h_rhs_e, h_rhs0_e]
    convert goal_e

--整数版。後ろで使われている。
lemma ideal_and_deletion_z {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2) (ground_v_none : ¬ F.sets (F.ground \ {x})) :
  (total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily:ℤ) = (total_size_of_hyperedges (deletion F.toSetFamily x hx ground_ge_two):ℤ) + ((F.ground.card:ℤ) - 1):=
  by
    rw [ideal_and_deletion F x hx ground_ge_two ground_v_none]
    simp_all
    rw [Int.natCast_sub]
    simp_all only [ge_iff_le, Nat.cast_one]
    exact Nat.le_of_succ_le ground_ge_two

--後ろで使われている。idealdeletionよりも、deletionを使うという手もある。
theorem hyperedge_totalsize_deletion_contraction_none {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred F.sets] (ground_v_none : ¬ F.sets (F.ground \ {x})) (singleton_have : F.sets {x}) :
  ((total_size_of_hyperedges F.toSetFamily):ℤ) + ((F.ground.card:ℤ) - 1)=
  (total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily:ℤ)  +
  (total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two):ℤ) + ((degree F.toSetFamily x):ℤ) :=
  by
    calc
      ((total_size_of_hyperedges F.toSetFamily):ℤ) + ((F.ground.card:ℤ) - 1)
          = (total_size_of_hyperedges (deletion F.toSetFamily x hx ground_ge_two):ℤ)  +
            (total_size_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily:ℤ) + ((degree F.toSetFamily x):ℤ) + ((F.ground.card:ℤ) - 1) := by
             rw [hyperedge_totalsize_deletion_contraction F x hx ground_ge_two singleton_have]

       _  = ((total_size_of_hyperedges (deletion F.toSetFamily x hx ground_ge_two):ℤ)  + ((F.ground.card:ℤ) - 1)) +
            (total_size_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily:ℤ) + ((degree F.toSetFamily x ):ℤ) := by
             ring

       _  = ((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ)  +
            (total_size_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily:ℤ) + ((degree F.toSetFamily x):ℤ) := by
              simp_all only [ideal_and_deletion_z F x hx ground_ge_two ground_v_none]

--omit [Nonempty α] in
lemma conv_deletion (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2) :
   normalized_degree_sum (idealdeletion F x hx ground_ge_two).toSetFamily =2*total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily  - (idealdeletion F x hx ground_ge_two).toSetFamily.ground.card*number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily :=
  by
    rw [normalized_degree_sum]
    simp_all
    ring_nf

--omit [Nonempty α] in
lemma conv_contraction (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2) :
   normalized_degree_sum (contraction F.toSetFamily x hx ground_ge_two) =2*total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)  - (contraction F.toSetFamily x hx ground_ge_two).ground.card*number_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two) :=
  by
    rw [normalized_degree_sum]
    simp_all
    ring_nf

--omit [Nonempty α] in
lemma conv_contraction_family (F : IdealFamily α) (x : α) (ground_ge_two: F.ground.card ≥ 2)(singleton_have: F.sets {x}) :
   normalized_degree_sum (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily =2*total_size_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily  - (contraction_ideal_family F x singleton_have ground_ge_two).ground.card*number_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily :=
  by
    rw [normalized_degree_sum]
    simp_all
    ring_nf

--IdealMain.leanで使われている。
theorem hyperedge_average_none {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred F.sets] (ground_v_none : ¬ F.sets (F.ground \ {x})) (singleton_have : F.sets {x}) :
  normalized_degree_sum F.toSetFamily + (F.ground.card:ℤ)=
  normalized_degree_sum (idealdeletion F x hx ground_ge_two).toSetFamily  +
  normalized_degree_sum (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily
  + 2*((degree F.toSetFamily x):ℤ) - ((number_of_hyperedges F.toSetFamily):ℤ) + 1 :=
  by

    calc
     normalized_degree_sum F.toSetFamily + (F.ground.card:ℤ)
    = 2*((total_size_of_hyperedges F.toSetFamily):ℤ) - (F.ground.card:ℤ)*((number_of_hyperedges F.toSetFamily):ℤ) + (F.ground.card:ℤ) :=
      by
        dsimp [normalized_degree_sum]
        simp_all
        ring_nf
        have comm0: (F.ground.card:ℤ)*(number_of_hyperedges F.toSetFamily:ℤ) = (number_of_hyperedges F.toSetFamily:ℤ)*(F.ground.card:ℤ) := by
         ring_nf
        rw [comm0]
        rw [sub_eq_add_neg]
        rw [add_comm]
        congr
  _ = 2*((total_size_of_hyperedges F.toSetFamily:ℤ) + ((F.ground.card:ℤ) - 1)) - (F.ground.card:ℤ)*(number_of_hyperedges F.toSetFamily:ℤ) - (F.ground.card:ℤ) + 2:= by
    ring_nf
  _ = 2*(((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ)  +
            (total_size_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily:ℤ) + ((degree F.toSetFamily x):ℤ)) - (F.ground.card:ℤ)*((number_of_hyperedges F.toSetFamily):ℤ)  - (F.ground.card:ℤ) + 2:= by
      rw [hyperedge_totalsize_deletion_contraction_none F x hx ground_ge_two ground_v_none singleton_have]
      simp_all only [add_left_inj, sub_left_inj, mul_eq_mul_left_iff, add_right_inj, Nat.cast_inj,
        OfNat.ofNat_ne_zero, or_false]
      rfl

  _ = 2*((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ) +
            2*((total_size_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily):ℤ) + 2*((degree F.toSetFamily x):ℤ) - ((F.ground.card):ℤ)*((((number_of_hyperedges F.toSetFamily):ℤ)+1)-1) - (F.ground.card:ℤ) + 2 := by
            simp_all only [add_sub_cancel_right, add_left_inj, sub_left_inj]
            ring

  _ =  2*((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ)  +
            2*((total_size_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily):ℤ) + 2*((degree F.toSetFamily x):ℤ)
             - ((F.ground.card):ℤ)*((number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily:ℤ)  +  (((number_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily):ℤ)-1)) - (F.ground.card:ℤ) + 2:= by
            rw [hyperedge_count_deletion_contraction_none_z F x hx ground_ge_two ground_v_none singleton_have]
            simp_all only [add_left_inj, sub_left_inj, sub_right_inj, mul_eq_mul_left_iff, Nat.cast_eq_zero,
              Finset.card_eq_zero]
            apply Or.inl
            ring
  _ = (2*((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ)  - ((F.ground.card:ℤ) - 1)*((number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ))
     + (2*((total_size_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily):ℤ) - ((F.ground.card:ℤ) - 1)*((number_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily):ℤ))
       +2*((degree F.toSetFamily x):ℤ)-((number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ) - ((number_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily):ℤ)
       + 2:= by
          simp_all only [add_left_inj]
          ring_nf

  _ = (2*((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ)  - (((idealdeletion F x hx ground_ge_two).toSetFamily.ground.card):ℤ)*((number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ))
     + (2*((total_size_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily):ℤ) - (((contraction_ideal_family F x singleton_have ground_ge_two).ground.card:ℤ))*((number_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily):ℤ))
       +2*((degree F.toSetFamily x):ℤ)-((number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ) - ((number_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily):ℤ)
        + 2:= by
         rw [ground_deletion]

         rw [ground_contraction_family]
         congr
         simp_all only [ge_iff_le]
         omega
         simp_all only [ge_iff_le]
         omega
  _ = normalized_degree_sum ((idealdeletion F x hx ground_ge_two).toSetFamily)  +
          normalized_degree_sum (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily  +2*((degree F.toSetFamily x):ℤ)
          -(number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily + number_of_hyperedges (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily)
          + 2:= by
           simp_all only [conv_deletion, conv_contraction_family]
           ring_nf
  _ = normalized_degree_sum ((idealdeletion F x hx ground_ge_two).toSetFamily)  +
          normalized_degree_sum (contraction F.toSetFamily x hx ground_ge_two)
          +2*((degree F.toSetFamily x):ℤ) - (((number_of_hyperedges F.toSetFamily):ℤ)+1) + 2:= by
           rw [←(hyperedge_count_deletion_contraction_none_z F x hx ground_ge_two ground_v_none singleton_have)]
           simp_all only [add_left_inj, sub_left_inj, add_right_inj]
           rfl
  _ = normalized_degree_sum (idealdeletion F x hx ground_ge_two).toSetFamily  +
       normalized_degree_sum (contraction F.toSetFamily x hx ground_ge_two)
       +2*((degree F.toSetFamily x):ℤ) - ((number_of_hyperedges F.toSetFamily):ℤ) + 1 :=
        by
          ring_nf

  --{x}がhyperedgeと仮定しないとcontraction_ideal_familyに揃えられない。IdealMainで使われている。
  theorem hyperedge_average_have {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)
  [DecidablePred F.sets] (hx_hyperedge : F.sets (F.ground \ {x})) (singleton_have : F.sets {x}) :
  normalized_degree_sum F.toSetFamily =
  normalized_degree_sum (idealdeletion F x hx ground_ge_two).toSetFamily  +
  normalized_degree_sum (contraction_ideal_family F x singleton_have ground_ge_two).toSetFamily
  +2*((degree F.toSetFamily x):ℤ) - ((number_of_hyperedges F.toSetFamily):ℤ) :=
  by
    --#check hyperedge_count_deletion_contraction_have_z F x hx ground_ge_two hx_hyperedge
    calc
     normalized_degree_sum F.toSetFamily
    = 2*((total_size_of_hyperedges F.toSetFamily):ℤ) - (F.ground.card:ℤ)*((number_of_hyperedges F.toSetFamily):ℤ) :=
      by
        dsimp [normalized_degree_sum]
        simp_all
        ring_nf
        have comm0: (F.ground.card:ℤ)*(number_of_hyperedges F.toSetFamily:ℤ) = (number_of_hyperedges F.toSetFamily:ℤ)*(F.ground.card:ℤ) := by
         ring_nf
        rw [comm0]
        rw [sub_eq_add_neg]
        rw [add_comm]
        congr
  _ = 2*((total_size_of_hyperedges F.toSetFamily:ℤ) + ((F.ground.card:ℤ) - 1)) - (F.ground.card:ℤ)*((number_of_hyperedges F.toSetFamily):ℤ) - 2*(F.ground.card:ℤ) + 2:= by
    ring_nf
  _ = 2*(((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ)  +
            ((total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)):ℤ) + ((degree F.toSetFamily x):ℤ) + ((F.ground.card:ℤ) - 1))
            - (F.ground.card:ℤ)*((number_of_hyperedges F.toSetFamily):ℤ) - 2*(F.ground.card:ℤ) + 2:= by
              rw [hyperedge_totalsize_deletion_contraction_have_z F x hx ground_ge_two hx_hyperedge]
  _ = 2*((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ) + 2*((total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)):ℤ)
      + 2*  ((degree F.toSetFamily x):ℤ)  - (F.ground.card:ℤ)*((number_of_hyperedges F.toSetFamily):ℤ) :=
      by
        ring_nf
  _ =  2*((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ)  + 2*((total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)):ℤ)
      + 2*((degree F.toSetFamily x):ℤ)
      - ((F.ground.card):ℤ)*(((number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ)  +  ((number_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)):ℤ)) :=
             by
               rw [hyperedge_count_deletion_contraction_have_z F x hx ground_ge_two hx_hyperedge singleton_have]
               simp_all only [sub_right_inj, mul_eq_mul_left_iff, add_right_inj, Nat.cast_inj, Nat.cast_eq_zero,
                 Finset.card_eq_zero]
               apply Or.inl
               rfl
  _ = 2*((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ) -  (((F.ground.card):ℤ) - 1)*((number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ)
     + 2*((total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)):ℤ) - (((F.ground.card):ℤ) - 1)*((number_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)):ℤ)
     + 2*((degree F.toSetFamily x):ℤ) - ((number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ) - ((number_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)):ℤ) :=
     by
       ring_nf
  _ = 2*((total_size_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ) - (((idealdeletion F x hx ground_ge_two).toSetFamily.ground.card:ℤ))*((number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ)
     + 2*((total_size_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)):ℤ) - (((contraction F.toSetFamily x hx ground_ge_two).ground.card:ℤ))*((number_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)):ℤ)
     + 2*((degree F.toSetFamily x):ℤ) - ((number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily):ℤ) - ((number_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)):ℤ) :=
     by
       rw [ground_deletion]
       rw [ground_contraction]
       congr
       simp_all only [ge_iff_le]
       omega
       simp_all only [ge_iff_le]
       omega
  _ = normalized_degree_sum ((idealdeletion F x hx ground_ge_two).toSetFamily)  +
          normalized_degree_sum (contraction F.toSetFamily x hx ground_ge_two)
          +2*((degree F.toSetFamily x):ℤ)
          -(number_of_hyperedges (idealdeletion F x hx ground_ge_two).toSetFamily + number_of_hyperedges (contraction F.toSetFamily x hx ground_ge_two)) :=
        by
          simp_all only [conv_deletion, conv_contraction]
          ring_nf
  _ = normalized_degree_sum ((idealdeletion F x hx ground_ge_two).toSetFamily)  + normalized_degree_sum (contraction F.toSetFamily x hx ground_ge_two)
       +2*((degree F.toSetFamily x):ℤ) - ((number_of_hyperedges F.toSetFamily):ℤ) :=
        by
          rw [hyperedge_count_deletion_contraction_have_z F x hx ground_ge_two hx_hyperedge singleton_have]
          simp_all only [sub_right_inj, add_right_inj, Nat.cast_inj]
          rfl
  _ = normalized_degree_sum (idealdeletion F x hx ground_ge_two).toSetFamily  +
       normalized_degree_sum (contraction F.toSetFamily x hx ground_ge_two)
       +2*((degree F.toSetFamily x):ℤ) - ((number_of_hyperedges F.toSetFamily):ℤ) :=
        by
          ring_nf

end Ideal
