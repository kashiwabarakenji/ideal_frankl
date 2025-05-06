import Mathlib.Order.Defs.PartialOrder
--import Mathlib.Order.Cover
--import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.DirectProduct
import rooted.functionalPartialTrace
import rooted.functionalDirectProduct

open Finset Set Classical SetupPoComponent

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable instance : ∀ v, Decidable (Quotient.mk'' v = q) :=  fun v => (Quotient.mk'' v).decidableEq q

lemma disjoint_ground_excl (s : Setup_po α) (q : Quotient (proj_setoid s)) [DecidableRel (projr s)][DecidableEq (Quotient (proj_setoid s))]
  --(hnonempty : (excl_po_V' s q).Nonempty) :
  (geq2quotient: (numClasses (proj_setoid s) ≥ 2)) :
  (comp_po s q).V ∩ (excl_po s q geq2quotient).V = ∅ :=
by
  dsimp [comp_po, excl_po]
  dsimp [comp_po_V', excl_po_V']
  dsimp [compFinset, exclFinset]

  by_contra h_contra
  change (comp_po s q).V ∩ (excl_po s q geq2quotient).V ≠ ∅ at h_contra
  rw [←Finset.nonempty_iff_ne_empty] at h_contra
  dsimp [comp_po, excl_po] at h_contra
  dsimp [comp_po_V', excl_po_V'] at h_contra
  dsimp [compFinset, exclFinset] at h_contra

  obtain ⟨v, h_v⟩ := h_contra

  rw [Finset.mem_inter] at h_v
  rw [Finset.mem_image] at h_v
  rw [Finset.mem_image] at h_v
  obtain ⟨h1,v1,hv1,veq⟩ := h_v
  simp at h1 hv1
  obtain ⟨h2,v2,hv2,veq2⟩ := h1
  subst veq
  simp_all only [ge_iff_le, Subtype.coe_eta]
  simp_all only [coe_mem]
  obtain ⟨val, property⟩ := v1
  contradiction

theorem directProduct_comp_excel  (s : Setup_po α) (q : Quotient (proj_setoid s)) [DecidableRel (projr s)][DecidableEq (Quotient (proj_setoid s))]
  (geq2quotient: (numClasses (proj_setoid s) ≥ 2)) :
  DirectProduct (partialorder_ideal_system (comp_po s q)).toSetFamily (partialorder_ideal_system (excl_po s q geq2quotient)).toSetFamily =
  (partialorder_ideal_system s).toSetFamily :=
by
  dsimp [partialorder_ideal_system]
  dsimp [comp_po, excl_po]
  dsimp [comp_po_V', excl_po_V']
  dsimp [compFinset, exclFinset]
  dsimp [DirectProduct]
  simp
  constructor
  ·
   simp_all only [ge_iff_le]
   ext a : 1
   simp_all only [Finset.mem_union, Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists,
      exists_and_right, exists_eq_right]
   apply Iff.intro
   · intro a_1
     simp at a_1
     cases a_1 with
     | inl h =>
        obtain ⟨w, h⟩ := h
        subst h
        simp_all only
     | inr h_1 =>
        obtain ⟨w, h⟩ := h_1
        simp_all only
   · intro a_1
     simp_all only [exists_true_left]
     tauto
  · funext ss
    simp
    --以下はs.Vの2分割になっている。
    let compq := Finset.image Subtype.val (filter (fun v => Quotient.mk'' v = q) s.V.attach)
    let eclq := Finset.image Subtype.val (filter (fun v => ¬ (⟦v⟧ = q))    s.V.attach)
    have : compq ∪ eclq = s.V :=
    by
      dsimp [compq, eclq]
      ext x
      apply Iff.intro
      · intro a_1
        simp at a_1
        cases a_1 with
        | inl h =>
          obtain ⟨w, h⟩ := h
          subst h
          simp_all only [ge_iff_le, Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists,
            exists_and_right, exists_eq_right]
        | inr h_1 =>
          obtain ⟨w, h⟩ := h_1

          simp_all only [ge_iff_le, Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists,
            exists_and_right, exists_eq_right]
      · intro hx
        by_cases Q : @Quotient.mk'' _ (proj_setoid s) ⟨x,hx⟩= q
        case pos =>
          simp_all only [ge_iff_le, Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists,
            exists_and_right, exists_eq_right]
          subst Q
          simp_all only [Finset.mem_union, Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists,
            exists_and_right, exists_eq_right, exists_apply_eq_apply, exists_true_left, true_or]
        case neg =>
          simp_all only [ge_iff_le, Finset.mem_union, Finset.mem_image, mem_filter, mem_attach, true_and,
            Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, compq, eclq]
          exact Or.inr Q
    have : compq ∩ eclq = ∅ := by
      dsimp [compq, eclq]
      let dge := disjoint_ground_excl s q geq2quotient
      dsimp [comp_po, excl_po] at dge
      dsimp [comp_po_V', excl_po_V'] at dge
      dsimp [compFinset, exclFinset] at dge
      convert dge

    constructor
    · intro a_1
      obtain ⟨comp_s, a_12, a_1⟩ := a_1 --comp_sはssのq側
      obtain ⟨comp1, comp2⟩ := a_12
      obtain ⟨ecl_s, a_14, unions⟩ := a_1 --ecl_sはssのnot q側
      obtain ⟨ecl1, ecl2⟩ := a_14

      --compqとeclqは、ssのq側とnot q側に分割するもの。

      have comp1' : comp_s ⊆ compq :=
      by
        dsimp [compq]
        convert comp1
      have : compq ⊆ s.V :=
      by
        dsimp [compq]
        intro x hx
        subst unions
        simp_all only [ge_iff_le, Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists,
          exists_and_right, exists_eq_right]
        obtain ⟨w, h⟩ := hx
        subst h
        simp_all only [Quotient.eq]

      have inc_comp: comp_s ⊆ s.V :=
      by

        exact @subset_trans _ _ _ comp_s compq s.V comp1' this

      have ecl1' : eclq ⊆ s.V :=
      by
        dsimp [eclq]
        intro x hx
        subst unions
        simp_all only [ge_iff_le, Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists,
          exists_and_right, exists_eq_right, eclq, compq]
        obtain ⟨w, h⟩ := hx
        simp_all only [eclq, compq]

      have : ecl_s ⊆ eclq :=
      by
        dsimp [eclq]
        intro x hx
        subst unions
        rw [Finset.mem_image]
        simp
        simp_all only [ge_iff_le, eclq, compq]
        simpa using ecl1 hx

      have inc_ecl: ecl_s ⊆ s.V :=
      by
        exact @subset_trans _ _ _ ecl_s eclq s.V this ecl1'

      constructor
      · intro v hv
        show v ∈ s.V
        rw [unions] at hv
        have : comp_s ∪ ecl_s ⊆ s.V :=
        by
          subst unions
          simp_all only [ge_iff_le, Finset.mem_union]
          cases hv with
          | inl h =>
            rw [Finset.union_subset_iff]
            simp_all only [and_self]
          | inr h_1 => exact union_subset inc_comp inc_ecl

        exact this hv

      · intro vv hvv hvvs  --このvvはssの要素。
        intro v hv hv_ine  --vのほうがvvよりも小さい。
        have rel_equiv: @Quotient.mk'' _ (proj_setoid s) ⟨vv, hvv⟩ = @Quotient.mk'' _ (proj_setoid s) ⟨v, hv⟩ :=
        by
          subst unions
          simp_all only [ge_iff_le, Quotient.eq, Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists,
            exists_and_right, exists_eq_right, exists_true_left, exists_const]
          dsimp [proj_setoid]
          dsimp [projr]
          show proj_max s ⟨vv, hvv⟩ = proj_max s ⟨v, hv⟩
          -- 同じ極大要素にいくものは同じ同値類に入るということを補題で示す。
          apply (proj_max_quotient s ⟨vv, hvv⟩ ⟨v, hv⟩).mpr
          exact Eq.symm (quotient_order s ⟨v, hv⟩ ⟨vv, hvv⟩ hv_ine)

        show v ∈ ss
        rw [unions]
        -- a_122と_a_131を使うのか。
        --どこかで場合分けする？b2の同値類がq側かnot q側か？
        let vq := @Quotient.mk'' _ (proj_setoid s) ⟨vv,hvv⟩
        by_cases hvq :vq = q --このように分けるよりも、vvがq側かnot q側かで分けたほうがいいのでは？
        case pos => --compのほう。hvvs : vv ∈ comp_s ∨ vv ∈ ecl_sで左側。hvqからいえる。
          have vvincomp: vv ∈ comp_s :=
          by
            --vvは、ssの要素なので、unionsにより、comp_sかecl_sのどちらか。
            --ecl_sだとすると、ecl1より、vq=qに反する。補題にするか？どのような補題か？
            have vvincomp: vv ∈ compq := by
              dsimp [compq]
              rw [Finset.mem_image]
              simp
              use hvv
              exact hvq
            have : compq ∩ ss = comp_s :=
            by
              --dsimp [compq]
              rw [unions]
              have comp_inc: comp_s ⊆ compq := by
                exact comp1'
              have : ecl_s ⊆ eclq := by
                sorry --下で証明しているはず。
              have : compq ∩ ecl_s = ∅ := by
                --これは正しいのでAIに聞くと教えてくれそう。
                sorry
              show compq ∩ (comp_s ∪ ecl_s) = comp_s
              rw [@Finset.inter_union_distrib_left]
              rw [this]
              subst unions hvq
              simp_all only [ge_iff_le, Quotient.eq, Finset.mem_union, Finset.mem_image, mem_filter, mem_attach,
                true_and, Subtype.exists, exists_and_right, exists_eq_right, exists_apply_eq_apply,
                Finset.union_empty, Finset.inter_eq_right, compq, vq, eclq]
            rw [←this]
            rw [Finset.mem_inter]
            constructor
            · exact vvincomp
            · exact hvvs

          subst hvq
          simp_all only [Finset.mem_union, mem_filter, mem_attach, true_and, Subtype.exists,
            exists_and_right, exists_eq_right]
          left
          show v ∈ comp_s
          --comp2はおそらく使う。vvがcomp側だとvもcomp側。
          specialize comp2 vv hvv
          have : Quotient.mk'' ⟨vv, hvv⟩ = vq :=
          by
            subst unions
            simp_all only [ge_iff_le, true_or, Quotient.eq, forall_const, compq, vq, eclq]
          specialize comp2 this
          specialize comp2 vvincomp
          specialize comp2 v hv
          apply comp2
          · exact hv_ine
          · show Quotient.mk'' ⟨v, hv⟩ = vq
            --まだv in comp_sは証明されていないので使えない。
            --大小関係があれば、同じ連結成分という補題があるといいか。
            exact id (Eq.symm rel_equiv)

        case neg =>
          specialize ecl2 vv hvv
          rw [Finset.mem_union]
          right
          --apply ecl2は使わない？
          show v ∈ ecl_s
          have : ¬⟦⟨vv, hvv⟩⟧ = q :=
          by
            subst unions
            simp_all only [ge_iff_le, Quotient.eq, not_false_eq_true, forall_true_left, Finset.mem_union, compq, eclq,
              vq]
            exact hvq
            --vとvvが同じ連結成分で、vvがq側でないから、vもq側でない。

          specialize ecl2 this
          have vvinecl: vv ∈ ecl_s :=
          by
            show vv ∈ ecl_s
            sorry --compの方の未解決問題vvincompに対応している。
          specialize ecl2 vvinecl
          specialize ecl2 v hv
          apply ecl2
          have : Quotient.mk'' ⟨v, hv⟩ ≠ q :=
          by
            exact ne_of_eq_of_ne (id (Eq.symm rel_equiv)) hvq
          specialize ecl2 this
          · exact hv_ine
          · exact ne_of_eq_of_ne (id (Eq.symm rel_equiv)) hvq

    · intro a_1
      obtain ⟨a_11, a_1⟩ := a_1
      constructor
      · constructor
        · constructor
          · exact fun ⦃a⦄ a => a
          · intro a_2 a_3
            intro a_4 a_5 a_6 ha_6 hh hhh
            rw [Finset.mem_image]
            simp
            subst hh
            simp_all only [ge_iff_le, Quotient.eq, Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists,
              exists_and_right, exists_eq_right, exists_true_left, exists_const]

        · constructor
          · constructor
            · constructor
              ·
                simp_all only [ge_iff_le]
                rfl
              ·
                intro a x h a_2 a_3 x_1 h_1 a_4
                simp_all only [ge_iff_le, Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists,
                  exists_and_right, exists_eq_right, not_false_eq_true, exists_const]
            · --show ss = Finset.image Subtype.val (filter (fun v => Quotient.mk'' v = q) s.V.attach) ∪ ?right.h.mpr.h.right.w
              ext x
              apply Iff.intro
              · intro a_2
                simp at a_2
                have :x ∈ s.V :=
                by
                  simp_all only [ge_iff_le, compq, eclq]
                  exact a_11 a_2
                rw [Finset.mem_union]
                rw [Finset.mem_image]
                rw [Finset.mem_image]
                simp
                simp_all only [ge_iff_le, exists_true_left, compq, eclq]
                simp_all only [compq, eclq]
                tauto
              · intro a_2
                --a_1やa2などを使うのか？まだ証明まで遠そう。
                -- a_1 : ∀ (a : α) (b : a ∈ s.V), a ∈ ss → ∀ (a_4 : α) (b_1 : a_4 ∈ s.V), ⟨a_4, b_1⟩ ≤ ⟨a, b⟩ → a_4 ∈ ss
                -- a_2 : x ∈ Finset.image Subtype.val (filter (fun v => Quotient.mk'' v = q) s.V.attach) ∪ Finset.image Subtype.val (filter (fun v => ¬⟦v⟧ = q) s.V.attach)
                show x ∈ ss
                sorry
















/-
example {A:Prop} {B:Prop} {C:Prop}:
   A∨B →  (A→C) → (B→C) → C :=
by
-/
