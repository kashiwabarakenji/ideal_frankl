import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne
import rooted.Parallel
import rooted.functionalCommon
import rooted.functionalTreePartialorder
import rooted.functionalSPO
import rooted.functionalSPO2
import rooted.functionalTreeIdeal
import rooted.functionalIdealrare
import rooted.functionalTraceIdeal

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

--excessが0であれば、同値類の大きさがすべて1。
lemma excess_zero (s: Setup_spo2 α) :
  excess s = 0 → ∀ q: Quotient s.setoid, (classOf s.toSetup_spo q).card = 1 :=
by
  intro h q
  have : ∀ q' :  Quotient s.setoid,0 ≤ (classOf s.toSetup_spo q').card - 1  := by
    intro q'
    simp_all only [zero_le]

  have nonneg: ∀ i ∈ Finset.univ, 0 ≤ Int.ofNat (#(classOf s.toSetup_spo i)) - 1 := by
    intro i a
    simp_all only [zero_le, implies_true, Finset.mem_univ]
    simp_all only [Int.ofNat_eq_coe, sub_nonneg, Nat.one_le_cast, one_le_card]
    simp only [classOf_nonempty]
  let fsez := @Finset.sum_eq_zero_iff_of_nonneg _ Int _ (fun q' => (classOf s.toSetup_spo q').card - 1) (Finset.univ : Finset (Quotient s.setoid)) nonneg
  --let con := classOf_nonempty s.toSetup_spo q
  dsimp [excess] at h
  have :∀ i ∈ Finset.univ, (fun q' => Int.ofNat (#(classOf s.toSetup_spo q')) - 1) i = 0 :=
  by
    intro i a
    simp_all only [Finset.mem_univ, Int.ofNat_zero, Int.ofNat_one, Int.ofNat_sub]
    apply fsez.mp
    simp
    have h_cast :
      (∑ q : Quotient s.setoid, (Int.ofNat (#(classOf s.toSetup_spo q)) - 1 : ℤ))
        =
      Int.ofNat (∑ q : Quotient s.setoid, (#(classOf s.toSetup_spo q) - 1)) :=
    by
      simp [Int.cast_sum]  -- ℕ の和を ℤ にキャスト
      let fssd := @Finset.sum_sub_distrib _ _ (Finset.univ : Finset (Quotient s.setoid)) (fun q' => Int.ofNat (#(classOf s.toSetup_spo q'))) (fun q' => 1) _
      suffices (∑ x : Quotient s.setoid, Int.ofNat (#(classOf s.toSetup_spo x))) - Int.ofNat (Fintype.card (Quotient s.setoid)) =
  ∑ x : Quotient s.setoid,   (Int.ofNat (#(classOf s.toSetup_spo x)) - 1) from by

        have :∀ q':Quotient s.setoid, Int.ofNat ((#(classOf s.toSetup_spo q')) - 1) = Int.ofNat (#(classOf s.toSetup_spo q')) - 1 := by
          intro q'
          simp [Int.ofNat_sub]
          have h_card_ge : 1 ≤ #(classOf s.toSetup_spo q') := by
            specialize nonneg q' (Finset.mem_univ _)
            -- 0 ≤ ↑n - 1 ⇒ n ≥ 1
            -- Int.ofNat n - 1 ≥ 0 ⇒ Int.ofNat n ≥ 1 ⇒ n ≥ 1
            simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true, Int.ofNat_eq_coe,
              sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, sub_nonneg, Nat.one_le_cast, one_le_card]

          rw [Nat.cast_sub  h_card_ge] --(#(classOf s.toSetup_spo q')) 1
          simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true, Int.ofNat_eq_coe,
            sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, one_le_card, Nat.cast_one]

        simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true, Int.ofNat_eq_coe,
          CharP.cast_eq_zero, sum_const_zero]
        intro i_1
        simp_all only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
        rw [this]
      rw [fssd]
      simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true, Int.ofNat_eq_coe, sum_const,
        card_univ, nsmul_eq_mul, mul_one]
    simp_all

    simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true]

  let ts := this q
  have :q ∈ Finset.univ := by
    exact Finset.mem_univ q
  specialize ts this
  simp at ts
  have h_eq : Int.ofNat (#(classOf s.toSetup_spo q)) - 1 + 1= 1 := by
    simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true, Int.ofNat_eq_coe, zero_add]
  simp at h_eq
  simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true, Int.ofNat_eq_coe, Nat.cast_one,
    sub_self]

--trace_parallel_average_rare を使って大きさ2以上の同値類の頂点をtraceすると、normalized degree sumが下がらないことを証明する。
--一般的な枠組みでは、trace_parallel_average_rareで証明済み。
theorem trace_ideal_nds_increase (s: Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x
)).card ≥ 2) :
  (spo_closuresystem s.toSetup_spo).normalized_degree_sum ≤ ((spo_closuresystem s.toSetup_spo).toSetFamily.trace x.val (by simp_all only [ge_iff_le,
    coe_mem] ) (by
  have :s.V = (spo_closuresystem s.toSetup_spo).ground := by
    simp_all only [ge_iff_le]
    obtain ⟨val, property⟩ := x
    rfl
  have : s.V.card ≥ 2:= by
    let csl := card_subtype_le_original  (classOf s.toSetup_spo ⟦x⟧)
    linarith
  exact this
    )).normalized_degree_sum :=
by
  have : s.V.card = (spo_closuresystem s.toSetup_spo).ground.card := by
    simp_all only [ge_iff_le]
    obtain ⟨val, property⟩ := x
    rfl

  let tpar := trace_parallel_average_rare (spo_closuresystem s.toSetup_spo) x (by simp_all only [ge_iff_le, coe_mem])
  have :∃ y, ↑x ≠ y ∧ parallel (spo_closuresystem s.toSetup_spo) (↑x) y :=
  by
    let xx := representativeNeSelf2 s.toSetup_spo x hx
    use xx
    constructor
    · dsimp [xx]
      dsimp [representativeNeSelf2]
      have rprop : (representativeNeSelf s.toSetup_spo x hx).val ∈ s.V.erase x.val := by
        exact coe_mem (representativeNeSelf s.toSetup_spo x hx)
      rw [Finset.mem_erase] at rprop
      exact rprop.1.symm
    · dsimp [xx]
      dsimp [representativeNeSelf2]
      have :s.setoid (representativeNeSelf2 s.toSetup_spo x hx) x := by
        exact representativeNeSelf_mem_classOf3 s.toSetup_spo x hx
      have :s.setoid x (representativeNeSelf2 s.toSetup_spo x hx) := by
        exact id (Setoid.symm' s.setoid this)
      let sce := spo_closuresystem_equiv2 s.toSetup_spo x (representativeNeSelf2 s.toSetup_spo x hx) this
      have :x ≠ representativeNeSelf2 s.toSetup_spo x hx := by
        dsimp [representativeNeSelf2]
        have rprop : (representativeNeSelf s.toSetup_spo x hx).val ∈ s.V.erase x.val := by
          exact coe_mem (representativeNeSelf s.toSetup_spo x hx)
        rw [Finset.mem_erase] at rprop
        let rp1s := rprop.1.symm
        exact fun a => rp1s (congrArg Subtype.val a)
      have : parallel (spo_closuresystem s.toSetup_spo) ↑x ↑(representativeNeSelf2 s.toSetup_spo x hx) :=
      by
        simp at sce
        cases sce
        case inr h =>
          exact False.elim (this h)
        case inl h =>
          exact h
      exact this

      --parallelとsetoidの関係
  specialize tpar this
  have : (spo_closuresystem s.toSetup_spo).is_rare ↑x :=
  by
    exact spo2_rare s ⟦x⟧ hx x rfl
  specialize tpar this
  exact tpar

--ただのSetupと比較するとシンプルになっている。
structure Setup_po (α : Type) [Fintype α] [DecidableEq α] where
(V : Finset α)
(nonemp   : V.Nonempty)
(f : V → V)
(po : PartialOrder V)
(order : ∀ x y : V, (reach f x y ↔ po.le x y)) --fからpo.leが決まる。

def partialorder_ideal_system (α : Type) [Fintype α] [DecidableEq α] (s: Setup_po α) : ClosureSystem α :=
{ ground := s.V,
  sets := fun ss : Finset α => ss ⊆ s.V ∧(∀ v : s.V, v.val ∈ ss → (∀ w : s.V, s.po.le w v → w.val ∈ ss)),
  inc_ground := by
    intro ss a
    exact a.1,
  has_ground := by
    simp
  nonempty_ground := by
    exact s.nonemp,
  intersection_closed := by
    intro s_1 t a a_1
    simp_all only [Subtype.forall, Finset.mem_inter, and_imp]
    obtain ⟨left, right⟩ := a
    obtain ⟨left_1, right_1⟩ := a_1
    apply And.intro
    · intro x hx
      simp_all only [Finset.mem_inter]
      obtain ⟨left_2, right_2⟩ := hx
      apply left left_2
    · intro a b a_1 a_2 a_3 b_1 a_4
      apply And.intro
      · tauto
      · tauto
}

--同値類の大きさが全部1のSetup_poに対して、対応するSetup_poを定義することができる。
--そして、idealの集合族が一致する。

theorem class_size_one_implies_eq (s: Setup_spo α) (x y: s.V) (ssl  : (⟦x⟧ : Quotient s.setoid) = ⟦y⟧) (hq1x :#(Finset.filter (fun a => @Quotient.mk'' _ s.setoid a = ⟦x⟧) s.V.attach) = 1) (hq1y :#(Finset.filter (fun a => @Quotient.mk'' _ s.setoid a = ⟦y⟧) s.V.attach) = 1) :
     (x : α) = y := by
  -- 同値類 `{ a | ⟦a⟧ = ⟦x⟧ }` のカードが 1 → その唯一元を取り出す
  have hcard :=
    (Finset.card_eq_one.mp hq1x)   -- ⟨z, hz_mem, huniq⟩
  --rcases hcard with ⟨z, hz_mem, huniq⟩
  obtain ⟨xx, hxx_mem⟩ := hcard

  -- `x` がその Finset に入っていることは自明
  have hx_mem :
      (x : {a // a ∈ s.V}) ∈ Finset.filter (fun a => @Quotient.mk'' _ s.setoid a = ⟦x⟧) s.V.attach := by
    -- `Quotient.mk'' x = ⟦x⟧` なので `simp`
    rw [Finset.mem_filter]
    simp_all only [Quotient.eq, mem_attach, and_self]


  -- `y` も `ssl : ⟦x⟧ = ⟦y⟧` から同じ Finset に入る
  have hy_mem :
      (y : {a // a ∈ s.V}) ∈ Finset.filter (fun a => @Quotient.mk'' _ s.setoid a = ⟦x⟧) s.V.attach := by
    rw [Finset.mem_filter]
    simp_all only [Quotient.eq, mem_attach, and_self]
    exact ⟨trivial, id (Setoid.symm' s.setoid ssl)⟩
  -- 「唯一性」より `x = z` と `y = z`
  have heq: xx = x := by
    simp_all only [Quotient.eq, Finset.mem_singleton, mem_filter, mem_attach, true_and]
  have : xx = y := by
    subst heq
    simp_all only [Quotient.eq, Finset.mem_singleton]
  subst heq this
  simp_all only [Quotient.eq, Finset.mem_singleton, Finset.card_singleton]

noncomputable def po_ideal_system_from_allone_le {α : Type} [Fintype α] [DecidableEq α] (s: Setup_spo α)  (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1): PartialOrder s.V :=
{
  le := fun (x y:s.V) => s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y),

  le_refl := by
    intro x
    exact s.spo.le_refl (@Quotient.mk s.V s.setoid x),

  le_trans := by
    intros x y z hxy hyz
    have sxy: s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) := by
      exact hxy
    have syz: s.spo.le (@Quotient.mk s.V s.setoid y) (@Quotient.mk s.V s.setoid z) := by
      exact hyz
    have sxz: s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid z) := by
      exact s.spo.le_trans (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) (@Quotient.mk s.V s.setoid z) sxy syz
    exact sxz,

  le_antisymm := by
    intros x y hxy hyx
    have sxy: s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) := by
      exact hxy
    have syx: s.spo.le (@Quotient.mk s.V s.setoid y) (@Quotient.mk s.V s.setoid x) := by
      exact hyx
    let ssl := s.spo.le_antisymm (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) sxy syx
    dsimp [classOf] at hq1
    let hq1x := hq1 (@Quotient.mk s.V s.setoid x)
    let hq1y := hq1 (@Quotient.mk s.V s.setoid y)

    let csoi := class_size_one_implies_eq s x y ssl hq1x hq1y
    exact Subtype.eq csoi
}

--hq1が成り立つ時は、同値類と要素が全単射が存在して、お互いのreachが対応していることも示すか。
--最終的には大小関係が対応していることを示す。

lemma po_ideal_system_from_allone_lem (α : Type) [Fintype α] [DecidableEq α] (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) (x y : s.V)(n:Nat):
 s.fq^[n] (@Quotient.mk s.V s.setoid x) = (@Quotient.mk s.V s.setoid y) ↔ (fun x => (s.fq ⟦x⟧).out)^[n] x = y:= by


  induction n generalizing x y with
  | zero =>
    simp
    let hq := hq1 (@Quotient.mk _ s.setoid x)
    dsimp [classOf] at hq
    simp at hq
    obtain ⟨z, hz_mem⟩ := Finset.card_eq_one.mp hq

    constructor
    · intro h
      have : z = x := by
        simp_all only [Finset.mem_singleton, Quotient.eq]
        have : x ∈ ({z}:Finset s.V) := by
          rw [←hz_mem]
          rw [Finset.mem_filter]
          constructor
          · exact mem_attach s.V x
          · exact (setroid_quotient s x x).mp rfl
        simp_all only [Finset.card_singleton, Finset.mem_singleton]

      have : y = z := by
        --simp_all only [Finset.mem_singleton, Quotient.eq]
        have : y ∈ ({z}:Finset s.V) := by
          rw [←hz_mem]
          rw [Finset.mem_filter]
          constructor
          · exact mem_attach s.V y
          · exact id (Setoid.symm' s.setoid h)
        rename_i this_1
        subst this_1
        simp_all only [Finset.mem_singleton, Finset.card_singleton]
      rename_i this_1
      subst this this_1
      simp_all only [Finset.card_singleton]
    · intro h
      subst h
      simp_all only [Finset.card_singleton]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := z
      rfl
  | succ n ih => --ih : s.fq^[n] ⟦x⟧ = ⟦y⟧ ↔ (fun x => (s.fq ⟦x⟧).out)^[n] x = y
    constructor
    · intro h --s.fq^[n + 1] ⟦x⟧ = ⟦y⟧
      show (fun x => (s.fq ⟦x⟧).out)^[n + 1] x = y
      have : s.fq^[n] (@Quotient.mk s.V s.setoid x) = (@Quotient.mk s.V s.setoid y) := by
        sorry

      dsimp [classOf] at hq1
      let hq1y := hq1 (@Quotient.mk s.V s.setoid y)
      have : (classOf s ⟦y⟧).card = 1 := by
        exact hq1y

      obtain ⟨z, hz_mem⟩ := Finset.card_eq_one.mp this

      have : y = z := by
        --simp_all only [Finset.mem_singleton, Quotient.eq]
        have : y ∈ ({z}:Finset s.V) := by
          rw [←hz_mem]
          dsimp [classOf]
          rw [Finset.mem_filter]
          constructor
          · exact mem_attach s.V y
          · exact rfl
        simp_all only [Finset.card_singleton, Finset.mem_singleton, true_iff, Function.iterate_succ,
          Function.comp_apply]
      rename_i this_1
      show  (fun x => (s.fq ⟦x⟧).out)^[n + 1] x = y
      sorry
      --simp_all only [Finset.card_singleton]

    · intro h
      subst h

      obtain ⟨val, property⟩ := x
      sorry


  --帰納法を使う必要がありそう。

noncomputable def po_ideal_system_from_allone (α : Type) [Fintype α] [DecidableEq α] (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1): Setup_po α :=
{ V := s.V,
  nonemp := by
    exact s.nonemp,
  f := fun x => Quotient.out (s.fq (@Quotient.mk _ s.setoid x)),
  po := po_ideal_system_from_allone_le s hq1,
  order := by
    intro x y
    dsimp [po_ideal_system_from_allone_le]
    constructor
    · intro hxy
      have :s.spo.le (@Quotient.mk s.V s.setoid x) (s.fq (@Quotient.mk s.V s.setoid x)) := by
        sorry
      have goal: s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) := by
        apply reach_leq s (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y)
        sorry
      --have : Quotient.out (s.fq (@Quotient.mk _ s.setoid x)) = Quotient.out (s.fq (@Quotient.mk _ s.setoid y)) := by
      --  sorry
      exact goal

    · intro hxy
      let rlr := reach_leq_rev s (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y)
      specialize rlr hxy
      show reach (fun x => (s.fq ⟦x⟧).out) x y
      --fとfqの対応がreachの対応になる。補題が必要。
      dsimp [reach]
      dsimp [reach] at rlr
      obtain ⟨n,hnl⟩ := rlr
      use n
      let pisf := po_ideal_system_from_allone_lem α s hq1 x y n
      exact (po_ideal_system_from_allone_lem α s hq1 x y n).mp hnl

      --帰納法を使う必要がありそう。








}
