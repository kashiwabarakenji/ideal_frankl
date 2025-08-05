import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
--import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne
import rooted.functionalCommon
import rooted.functionalTreePartialorder
import rooted.functionalSPO

-- We have collected the premises for Setup2 that feature ClosureSystem.
-- There are also some that are assumed to be Setup_spo in the second half.
--For traces involved, see TraceIdeal.

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

--Named pre2_closuresystem.Define hyperedge using s.po and setoid.
noncomputable def pre2_closuresystem (s: Setup2 α): ClosureSystem α :=
{
    ground := s.V,
    sets := fun ss =>
    ∃ (I : Finset (Quotient s.setoid)),
      (∀ q ∈ I, ∀ q', s.po.le q' q → q' ∈ I) ∧
      (ss ⊆ s.V) ∧ ((hs:ss⊆ s.V) → (∀ (x : α) (h : x ∈ ss), Quotient.mk s.setoid ⟨x, by exact hs h⟩ ∈ I) ∧ (∀ q ∈ I,  ∀ (x:s.V), Quotient.mk s.setoid ⟨x, by simp⟩ = q → x.val ∈ ss)),
    inc_ground := by
      intro s a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      simp_all only [forall_true_left]
    nonempty_ground := by
      exact s.nonemp

    has_ground := by
      use Finset.univ
      constructor
      · simp_all
      · simp_all only [subset_refl, Finset.mem_univ, implies_true, Subtype.coe_eta, coe_mem, imp_self, and_self]

    intersection_closed := by
      intro s t ⟨Ia, hIa, hsub_a, ha⟩ ⟨Ib, hIb, hsub_b, hb⟩
      let I := Ia ∩ Ib
      have hI : ∀ q ∈ I, ∀ q', q' ≤ q → q' ∈ I := by
        intro q hq q' hle
        simp only [Finset.mem_inter] at hq
        simp_all only [forall_true_left, Finset.mem_inter, I]
        simp_all only
        obtain ⟨left, right⟩ := hq
        apply And.intro
        · exact hIa q left q' hle
        · apply hIb
          on_goal 2 => {exact hle
          }
          · simp_all only
      use I
      constructor
      · exact hI
      constructor
      · simp_all only [forall_true_left, Finset.mem_inter, and_imp, I]
        simp_all only [I]
        exact inter_subset_left.trans hsub_a
      · intro hs
        constructor
        · intros x hx
          simp_all only [Subtype.coe_eta, Subtype.forall, forall_true_left, Finset.mem_inter, and_imp, I]
          simp_all only [I]
          obtain ⟨left, right⟩ := ha
          obtain ⟨left_1, right_1⟩ := hb
          apply And.intro
          · apply left
            simp_all only [Finset.mem_inter, I]
          · apply left_1
            simp_all only [Finset.mem_inter, I]
        · intros q hq x hx
          subst hx
          simp_all only [Subtype.coe_eta, Subtype.forall, forall_true_left, Finset.mem_inter, and_imp, I]
          simp_all only [I]
          obtain ⟨val, property⟩ := x
          obtain ⟨left, right⟩ := ha
          obtain ⟨left_1, right_1⟩ := hb
          obtain ⟨left_2, right_2⟩ := hq
          simp_all only [I]
          apply And.intro
          · apply right
            · exact left_2
            · congr
          · apply right_1
            · exact right_2
            · congr



}

--This theorem is the relationship between the ideal between preorder and partial order.The relationship with SPO is the later theorem.
-- You might also want to change the theorem name.It's like pre_pre2_closuresystem_eq.
-- Only used with functionalMain.
-- You might want to change the name so that it can be seen as a conversion to closuresystem.Pre_pre2_closuresystem_eq etc.
theorem Preorder_eq_PartialOrder (s: Setup2 α)  :
  pre_closuresystem s.toSetup = pre2_closuresystem s  := by
  ext ss
  · rfl
  ·
    dsimp [pre_closuresystem, pre2_closuresystem]
    let st := s.setoid

    apply Iff.intro
    · intro a
      obtain ⟨hs, hhs⟩ := a
      let I' := (Finset.univ : Finset s.V).filter (fun x =>
        ∀ a:s.V, st.r a x → a.val ∈ ss) |>.image (Quotient.mk st)
      use I'

      constructor
      · intro q hq q' hqq'
        dsimp [I'] at hq
        dsimp [I']
        rw [Finset.mem_image]
        rw [Finset.mem_image] at hq
        rcases Quotient.exists_rep q with ⟨y, hy⟩
        rcases Quotient.exists_rep q' with ⟨x, hx⟩
        use x
        simp
        constructor
        · intro aa bb
          intro h
          specialize hhs y
          have : y.val ∈ ss :=
          by
            subst hy hx
            simp_all only [Subtype.forall, mem_filter, Finset.mem_univ, true_and, Quotient.eq, AntisymmRel.setoid_r,
              Subtype.exists, st, I']
            obtain ⟨w, h_1⟩ := hq
            obtain ⟨w_1, h_1⟩ := h_1
            obtain ⟨left, right⟩ := h_1
            simp_all only [mem_attach, true_and, st, I']
            apply hhs
            · apply left
              · tauto
            · rfl
          specialize hhs this
          have : s.pre.le x y := by
            subst hy hx
            simp_all only [le_refl, Subtype.forall, coe_mem, mem_filter, Finset.mem_univ, true_and, Quotient.eq,
              AntisymmRel.setoid_r, Subtype.exists, st, I']
            exact pullback_preorder_lemma s ⟦x⟧ ⟦y⟧ x y rfl rfl hqq'
          have : s.pre.le ⟨aa,bb⟩ y := by
            suffices  s.pre.le ⟨aa,bb⟩ x from by
              subst hy hx
              simp_all only [le_refl, Subtype.forall, coe_mem, mem_filter, Finset.mem_univ, true_and, Quotient.eq,
                AntisymmRel.setoid_r, Subtype.exists, ge_iff_le, st, I']
              apply Preorder.le_trans ⟨aa, bb⟩ x y this
              simp_all only [mem_attach, true_and, st, I']
            subst hy hx
            simp_all only [le_refl, Subtype.forall, coe_mem, mem_filter, Finset.mem_univ, true_and, Quotient.eq,
              AntisymmRel.setoid_r, Subtype.exists, st, I']
            rw [s.h_setoid] at h
            dsimp [setoid_preorder] at h
            dsimp [AntisymmRel] at h
            exact AntisymmRel.ge (id (And.symm h))
          subst hy hx
          simp_all only [le_refl, Subtype.forall, coe_mem, mem_filter, Finset.mem_univ, true_and, Quotient.eq,
            AntisymmRel.setoid_r, Subtype.exists, st, I']
        ·
          subst hy hx
          simp_all only [Subtype.forall, mem_filter, Finset.mem_univ, true_and, Quotient.eq, AntisymmRel.setoid_r,
            Subtype.exists, st, I']

      · constructor
        · exact hs
        · intro hs
          constructor
          · intro x
            intro h
            simp_all only [Subtype.forall, Finset.mem_image, mem_filter, Finset.mem_univ,
              true_and, Quotient.eq, Subtype.exists, I', st]
            use x
            use (hs h)
            constructor
            · intro aa bb
              intro hh
              rw [s.h_setoid] at hh
              dsimp [setoid_preorder] at hh
              dsimp [AntisymmRel] at hh
              specialize hhs x
              have : x ∈ s.V := hs h
              specialize hhs this
              specialize hhs h
              specialize hhs aa bb
              simp_all only [forall_const, st, I']
            ·
              rw [s.h_setoid]

          · intro q hq x hx
            simp_all only [Subtype.forall, mem_filter, Finset.mem_univ, true_and, Quotient.eq, AntisymmRel.setoid_r,
              Subtype.exists, st, I']
            obtain ⟨val, property⟩ := x
            simp_all only [st, I']
            subst hx
            simp_all only [Finset.mem_image, mem_filter, Finset.mem_univ, true_and, Quotient.eq, AntisymmRel.setoid_r,
              Subtype.exists, st, I']
            obtain ⟨w, h⟩ := hq
            obtain ⟨w_1, h⟩ := h
            obtain ⟨left, right⟩ := h
            apply left
            · exact id (Setoid.symm' s.setoid right)


    · intro hi
      obtain ⟨I, hI⟩ := hi
      rw [s.h_po] at hI
      dsimp [partialOrder_from_preorder] at hI
      obtain ⟨left, right⟩ := hI


      constructor
      · simp_all only
      · intro v hv
        intro w a
        let q:= Quotient.mk st v
        let q':= Quotient.mk st w
        show ↑w ∈ ss

        have : q ∈ I := by
          simp_all only [st, q]
          obtain ⟨val, property⟩ := v
          obtain ⟨val_1, property_1⟩ := w
          obtain ⟨left_1, right⟩ := right
          simp_all only [forall_true_left, st]
        have qI: q' ∈ I := by
          specialize left q this q' a
          exact left
        dsimp [q'] at qI

        obtain ⟨left_1, right⟩ := right

        specialize right left_1
        obtain ⟨left_1, right ⟩ := right
        specialize left q this q' a
        have : q' = Quotient.mk st w := by
          rw [← @Quotient.mk''_eq_mk]

        rename_i II I3 I4
        have : ⟦w⟧ ∈ I := by
          simp_all only [st, q']
        have : ∀ qq ∈ I, {a:s.V | (Quotient.mk st a) = qq}.image Subtype.val ⊆ ss := by
          intro qq
          intro hqq
          simp_all only [Finset.mem_image, Subtype.val, mem_filter, Finset.mem_univ, true_and]
          simp
          intro y
          intro hy
          simp at hy
          simp
          have :  ⟦y⟧ ∈ I := by
            rw [←hy] at hqq
            exact hqq
          unfold Quotient at hqq
          subst hy
          simp_all only [st, q, q']
          obtain ⟨val, property⟩ := v
          obtain ⟨val_1, property_1⟩ := w
          obtain ⟨val_2, property_2⟩ := y
          simp_all only [st]
          simp_all only [Subtype.coe_eta, Subtype.forall, st]
          apply right
          · exact hqq
          · rfl

        have : s.po.le (Quotient.mk st w) (Quotient.mk st v) := by
          simp_all [q, q', st]
          obtain ⟨val, property⟩ := v
          obtain ⟨val_1, property_1⟩ := w
          simp_all only [st]
          exact pushforward_preorder_lemma s ⟨val_1, property_1⟩ ⟨val, property⟩ a

        have :q' ≤ q := by
          simp_all only [st, q, q']
        have wv: w ≤ v := by
          simp_all only [q', st, q]
        have aS: {a:s.V | (Quotient.mk st a) = q'}.image Subtype.val  ⊆ ss := by
          intro x
          intro h
          simp_all only [Subtype.val, mem_filter, Finset.mem_univ, true_and]
          show x ∈ ↑ss
          obtain ⟨y, hy⟩ := Quotient.exists_rep q'
          simp_all [st, q, q']
          obtain ⟨val, property⟩ := v
          obtain ⟨val_1, property_1⟩ := w
          obtain ⟨val_2, property_2⟩ := y
          obtain ⟨w, h⟩ := h
          simp_all only [st]
          apply right
          rename_i this_2
          exact this_2
          exact Quotient.sound h

        have : w ∈ {a:s.V | (Quotient.mk st a) = q'} := by
          simp_all only [Finset.mem_image, Subtype.val, mem_filter, Finset.mem_univ, true_and]
          simp_all only [Quotient.eq, AntisymmRel.setoid_r, Set.image_subset_iff, mem_setOf_eq, q', st, q]
          obtain ⟨val, property⟩ := v
          obtain ⟨val_1, property_1⟩ := w

          simp_all only [forall_true_left, st]
          rfl
        have : w.val ∈ {a:s.V | (Quotient.mk st a) = q'}.image Subtype.val := by
          simp_all only [Finset.mem_image, Subtype.val, mem_filter, Finset.mem_univ, true_and]
          simp_all only [Quotient.eq, AntisymmRel.setoid_r, Set.image_subset_iff, mem_setOf_eq, Subtype.exists,
            exists_and_right, exists_eq_right, Subtype.coe_eta, coe_mem, exists_const, q', st, q]
          simp_all only [Set.mem_image, mem_setOf_eq, Subtype.exists, exists_and_right, exists_eq_right,
            Subtype.coe_eta, coe_mem, exists_const, q, q', st]

        have : w.val ∈ ss := by
          exact aS this
        exact this

def spo_closuresystem (s: Setup_spo α) : ClosureSystem α :=
{
  ground := s.V,
    sets := fun ss =>
    ∃ (I : Finset (Quotient s.setoid)),
      (∀ q ∈ I, ∀ q', s.spo.le q' q → q' ∈ I) ∧
      (ss ⊆ s.V) ∧ ((hs:ss⊆ s.V) → (∀ (x : α) (h : x ∈ ss), Quotient.mk s.setoid ⟨x, by exact hs h⟩ ∈ I) ∧ (∀ q ∈ I,  ∀ (x:s.V), Quotient.mk s.setoid ⟨x, by simp⟩ = q → x.val ∈ ss)),
  inc_ground := by
    intro s a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    simp_all only [forall_true_left]
  nonempty_ground := by
    exact s.nonemp

  has_ground := by
    use Finset.univ
    constructor
    · simp_all
    · simp_all only [subset_refl, Finset.mem_univ, implies_true, Subtype.coe_eta, coe_mem, imp_self, and_self]

  intersection_closed := by
    intro ss t ⟨Ia, hIa, hsub_a, ha⟩ ⟨Ib, hIb, hsub_b, hb⟩
    let I := Ia ∩ Ib
    have hI : ∀ q ∈ I, ∀ q', s.spo.le q' q → q' ∈ I := by
      intro q hq q' hle
      simp only [Finset.mem_inter] at hq
      simp_all only [forall_true_left, Finset.mem_inter, I]
      simp_all only
      obtain ⟨left, right⟩ := hq
      apply And.intro
      · exact hIa q left q' hle
      · apply hIb
        on_goal 2 => {exact hle
        }
        · simp_all only
    use I
    constructor
    · exact hI
    constructor
    · simp_all only [forall_true_left, Finset.mem_inter, and_imp, I]
      simp_all only [I]
      exact inter_subset_left.trans hsub_a
    · intro hs
      constructor
      · intros x hx
        simp_all only [Subtype.coe_eta, Subtype.forall, forall_true_left, Finset.mem_inter, and_imp, I]
        simp_all only [I]
        obtain ⟨left, right⟩ := ha
        obtain ⟨left_1, right_1⟩ := hb
        apply And.intro
        · apply left
          simp_all only [Finset.mem_inter, I]
        · apply left_1
          simp_all only [Finset.mem_inter, I]
      · intros q hq x hx
        subst hx
        simp_all only [Subtype.coe_eta, Subtype.forall, forall_true_left, Finset.mem_inter, and_imp, I]
        simp_all only [I]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := ha
        obtain ⟨left_1, right_1⟩ := hb
        obtain ⟨left_2, right_2⟩ := hq
        simp_all only [I]
        apply And.intro
        · apply right
          · exact left_2
          · congr
        · apply right_1
          · exact right_2
          · congr
}

--I'm using it below.The setoid must be embedded.
lemma seteq_setupspo_eq  (s:Setup2 α) :
s.setoid = (setup_setupspo s).setoid := by
  dsimp [setup_setupspo]
--It took a while and proved without much understanding.
--Used with functionalMain.
--What about the name pre2_spo_closuresystem_eq?
theorem Setup_spo_eq_PartialOrder (s: Setup2 α)  :
  pre2_closuresystem s = spo_closuresystem (setup_setupspo s)  := by
  ext ss
  · rfl
  ·
    dsimp [pre2_closuresystem, spo_closuresystem]

    apply Iff.intro
    · intro a
      simp at a
      obtain ⟨hs, hhs⟩ := a
      use hs
      simp
      constructor
      · intro q hq q' hqq'
        obtain ⟨x, hx⟩ := Quotient.exists_rep q
        obtain ⟨x', hx'⟩ := Quotient.exists_rep q'

        have : s.V = (setup_setupspo s).V:= by
          exact rfl

        obtain ⟨hss1,hss2,hss3⟩ := hhs
        specialize hss3 hss2
        obtain ⟨hss31,hss32⟩ := hss3
        have : q ∈ hs := by
          specialize hss31 x
          have :x.val ∈ ss :=
          by
            simp_all only [coe_mem, Subtype.coe_eta, Quotient.eq, Quotient.out_eq]
            subst hx hx'
            apply hss32
            · exact hq
            · rfl
            · simp
          specialize hss31 this
          simp at hss31
          simp_all only [coe_mem]
        have :q' ∈ hs := by
          specialize hss1 q
          apply hss1 this
          exact reach_po_leq s q' q hqq'
        subst hx hx'
        simp_all only [coe_mem]
      · constructor
        ·
          obtain ⟨left, right⟩ := hhs
          obtain ⟨left_1, right⟩ := right
          exact left_1
        · intro hsss
          constructor
          · intro x
            intro h
            obtain ⟨left, right⟩ := hhs
            obtain ⟨left_1, right⟩ := right
            simp_all only [forall_true_left]
            obtain ⟨left_2, right⟩ := right
            exact left_2 x h
          · intro q hq x hx
            intro a
            subst a
            obtain ⟨left, right⟩ := hhs
            obtain ⟨left_1, right⟩ := right
            simp_all only [forall_true_left]
            obtain ⟨left_2, right⟩ := right
            apply right
            · exact hq
            · rfl
    . intro h
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      simp_all only [mem_mk, Subtype.coe_eta, Subtype.forall]
      obtain ⟨left_2, right⟩ := right
      simp_all only [forall_true_left]
      obtain ⟨left_3, right⟩ := right
      constructor
      swap
      · rw [seteq_setupspo_eq s]
        exact left
      · constructor
        · intro q hq q' hqq'
          simp
          specialize left_1 q hq q'
          apply left_1
          exact (spole_iff_po s q' q).mp hqq'
        ·
          constructor
          ·
            exact left_2
          · intro hs
            apply And.intro
            · intro x h
              exact left_3 x h
            · intro q a a_1 b a_2
              apply right
              · exact a
              · congr

--- The setiod equivalents must be parallel.
-- I've used it in several places.
-- The content is more parellel than equiv, but the next equiv2 will be the name of parallel.
lemma spo_closuresystem_equiv (s : Setup_spo α) (x y: s.V) (h: s.setoid.r x y) (hs: (spo_closuresystem s).sets ss):
  x.val ∈ ss ↔ y.val ∈ ss := by
    obtain ⟨left, right⟩ := hs
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    specialize right left_2
    obtain ⟨left_3, right⟩ := right
    apply Iff.intro
    · intro hss
      let q := Quotient.mk s.setoid x
      have : q ∈  left := by
        simp_all only [Subtype.coe_eta, Subtype.forall, q]
      specialize right q this
      specialize right y
      apply right
      exact Quotient.sound (id (Setoid.symm' s.setoid h))
    · intro hss
      let q := Quotient.mk s.setoid y
      have : q ∈  left := by
        simp_all only [Subtype.coe_eta, Subtype.forall, q]
      specialize right q this
      specialize right x
      apply right
      exact Quotient.sound h

--Used with TraceIdeal2.You can also include parallel in the theorem name.
lemma spo_closuresystem_equiv2 (s : Setup_spo α) (x y: s.V) (h: s.setoid.r x y) :
  parallel (spo_closuresystem s) x y ∨ x = y:=
by
  dsimp [parallel]
  by_cases hxy: x = y
  · right
    exact hxy
  ·
    constructor
    · constructor
      · simp_all only [coe_mem]
      · constructor
        · exact Subtype.coe_ne_coe.mpr hxy
        · intro ss hss
          exact spo_closuresystem_equiv s x y h hss
