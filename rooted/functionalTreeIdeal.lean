import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
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
import rooted.functionalCommon
--import rooted.functionalTreePreorder
import rooted.functionalTreePartialorder
import rooted.functionalSPO



open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

--PreorderOldにある定理をSetup2用に書き換え。
noncomputable def setoid_ideal_ClosureSystem (s: Setup2 α): ClosureSystem α :=
{
    ground := s.V,
    sets := fun ss =>
    ∃ (I : Finset (Quotient s.setoid)),
      (∀ q ∈ I, ∀ q', s.po.le q' q → q' ∈ I) ∧  -- ideal 条件
      (ss ⊆ s.V) ∧ ((hs:ss⊆ s.V) → (∀ (x : α) (h : x ∈ ss), Quotient.mk s.setoid ⟨x, by exact hs h⟩ ∈ I) ∧ (∀ q ∈ I,  ∀ (x:s.V), Quotient.mk s.setoid ⟨x, by simp⟩ = q → x.val ∈ ss)),
    inc_ground := by
      intro s a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      simp_all only [forall_true_left]
    nonempty_ground := by
      exact s.nonemp

    has_ground := by --Vがsetsになることを示す。そのときは、すべての同値類がIに含まれる。
      simp_all only
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

    /- こっちでも通る。どっちがよい。
    intersection_closed := by
      intro s t a b
      simp_all only --aもidealで、bもidealであるときに、a∩bもidealであることを示す。
      obtain ⟨Ia, hIa⟩ := a
      obtain ⟨Ib, hIb⟩ := b
      constructor
      · constructor
        · intro q hq q' hqq'
          obtain ⟨left, right⟩ := hIa
          obtain ⟨left_1, right_1⟩ := hIb
          apply left
          simpa
          simp_all only
        ·
          simp_all
          obtain ⟨left, right⟩ := hIa
          obtain ⟨left_1, right_1⟩ := hIb
          obtain ⟨left_2, right⟩ := right
          obtain ⟨left_3, right_1⟩ := right_1
          simp_all only [forall_true_left, implies_true, and_true]
          intro x hx
          simp_all only [Finset.mem_inter]
          obtain ⟨left_4, right_2⟩ := hx
          exact left_3 right_2
      -/

}

theorem Preorder_eq_PartialOrder (s: Setup2 α)  :
  preorder_ideal_system s.toSetup = setoid_ideal_ClosureSystem s  := by
  --#check @setoid_ideal_ClosureSystem _ _ V nonemp (@setoid_preorder V _:Setoid V) _
  --#check setoid_ideal_ClosureSystem V nonemp (@setoid_preorder V _)
  ext ss
  · rfl
  · --rename_i s
    --rcases s with ⟨s_val, hs⟩
    --unfold Membership.mem
    dsimp [preorder_ideal_system, setoid_ideal_ClosureSystem]
    let st := s.setoid

    apply Iff.intro
    · intro a --sはpreorderのidealで、その性質がaに入っている。
      obtain ⟨hs, hhs⟩ := a --hsはsがVの要素であること。hhsは、sのidealとしての性質。
      --Iは同値類の集まりなので、sを含む同値類を全部持ってくるとよい。
      --I'は、sを含む同値類の全体。
      let I' := (Finset.univ : Finset s.V).filter (fun x =>
        ∀ a:s.V, st.r a x → a.val ∈ ss) |>.image (Quotient.mk st)
      use I'
      --show (∀ q ∈ I', ∀ q' ≤ q, q' ∈ I') ∧ s ⊆ V ∧ ∀ (hs : s ⊆ V) (x : α) (h : x ∈ s), ⟦⟨x, ⋯⟩⟧ ∈ I'
      --示すべきことは、I'がidealになっていることと、sの要素の同値類が全部I'に入っていること。

      constructor
      · intro q hq q' hqq' --ここで使う性質は、I'の定義とhhs。qが大きい方で、q'が小さい方。q'がI'に入っていることを示すのが目標。
        dsimp [I'] at hq
        dsimp [I']
        rw [Finset.mem_image]
        rw [Finset.mem_image] at hq
        rcases Quotient.exists_rep q with ⟨y, hy⟩ --xはq'の代表元。
        rcases Quotient.exists_rep q' with ⟨x, hx⟩ --xはq'の代表元。
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
              --simp_all only [AntisymmRel.setoid_r, st, I']
              --rfl
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


    · intro hi --sはsetoidのidealで、その性質がaに入っている。
      obtain ⟨I, hI⟩ := hi --hIに同値類の順序が入っている。
      rw [s.h_po] at hI
      dsimp [partialOrder_from_preorder] at hI
      --分解するよりも定理を使った方がいい？
      --dsimp [s.setoid] at hI
      --dsimp [setoid_preorder] at hI
      --dsimp [quotient_partial_order] at hI
      -- rw [preorder_partialorder_lemma] at hI
      obtain ⟨left, right⟩ := hI


      constructor --sは、Iの半順序のideal。
      · simp_all only
      · intro v hv
        intro w a
        --left  ∀ q ∈ I, ∀ q' ≤ q, q' ∈ I
        --right s ⊆ V ∧ ∀ (hs : s ⊆ V) (x : α) (h : x ∈ s), ⟦⟨x, ⋯⟩⟧ ∈ I
        --obtain ⟨val, property⟩ := v
        --obtain ⟨val_1, property_1⟩ := w
        let q:= Quotient.mk st v
        let q':= Quotient.mk st w
        --simp_all only [forall_true_left]
        --simp_all only
        show ↑w ∈ ss
        --rcases Quotient.exists_rep q with ⟨y, hy⟩ --xはq'の代表元。
        --rcases Quotient.exists_rep q' with ⟨x, hx⟩ --xはq'の代表元

        have : q ∈ I := by
          simp_all only [st, q]
          obtain ⟨val, property⟩ := v
          obtain ⟨val_1, property_1⟩ := w
          obtain ⟨left_1, right⟩ := right
          simp_all only [forall_true_left, st]
        have qI: q' ∈ I := by
          -- Add necessary proof steps here
          specialize left q this q' a
          exact left
        dsimp [q'] at qI
        --preorderとorderの関係を使う必要があるかも。
        --rw [← @Quotient.mk''_eq_mk] at qI
        --dsimp [setoid_preorder] at qI  --このあとqI使ってない？
        --dsimp [preorder_partialorder_lemma] at qI
        --dsimp [setoid_preorder] at left

        obtain ⟨left_1, right⟩ := right --rightも使ってないかも。

        specialize right left_1
        obtain ⟨left_1, right ⟩ := right
        specialize left q this q' a
        have : q' = Quotient.mk st w := by
          rw [← @Quotient.mk''_eq_mk]

        --rw [s.h_setoid] at I
        --rw [setoid_preorder] at I
        --simp at right
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
          --simp  at hqq
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
          --rename_i inst inst_1 inst_2 inst_3 this_1 left_1_1 this_2 this_3 this_4 this_5
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
  -- Implement the closure system logic here
{
  ground := s.V,
    sets := fun ss =>
    ∃ (I : Finset (Quotient s.setoid)),
      (∀ q ∈ I, ∀ q', s.spo.le q' q → q' ∈ I) ∧  -- ideal 条件
      (ss ⊆ s.V) ∧ ((hs:ss⊆ s.V) → (∀ (x : α) (h : x ∈ ss), Quotient.mk s.setoid ⟨x, by exact hs h⟩ ∈ I) ∧ (∀ q ∈ I,  ∀ (x:s.V), Quotient.mk s.setoid ⟨x, by simp⟩ = q → x.val ∈ ss)),
  inc_ground := by
    intro s a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    simp_all only [forall_true_left]
  nonempty_ground := by
    exact s.nonemp

  has_ground := by --Vがsetsになることを示す。そのときは、すべての同値類がIに含まれる。
    simp_all only
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

--s Setup2のQuotientと、setup_setupspoのQuotientの対応の写像が必要。
noncomputable def setup_setupspo_quotient (s: Setup2 α) (q: Quotient s.setoid) : Quotient (setup_setupspo s).setoid :=
  let rep : s.V := Quotient.out q
  Quotient.mk (setup_setupspo s).setoid ⟨rep, by simp⟩

lemma seteq_setupspo_eq  (s:Setup2 α) :
s.setoid = (setup_setupspo s).setoid := by
  dsimp [setup_setupspo]

/- この補題がポイントだったと思ったけど、結果的につかってなかったみたい。
lemma setup_setupspo_quotient_lemma (s: Setup2 α) (q: Quotient s.setoid) :
  classOf (setup_setupspo s) (setup_setupspo_quotient s q) = eqClass_setup s.toSetup (Quotient.out q) := by
  let ec := eqClass_Class_of2 s q
  simp_all only [ec]
  simp [setup_setupspo_quotient]
-/

--時間がかかった上に、よくわからないまま証明された。
theorem Setup_spo_eq_PartialOrder (s: Setup2 α)  :
  setoid_ideal_ClosureSystem s = spo_closuresystem (setup_setupspo s)  := by
  ext ss --ssは集合族としてのideal
  · rfl
  ·
    dsimp [setoid_ideal_ClosureSystem, spo_closuresystem]
    --let st := s.setoid

    apply Iff.intro
    · intro a --sはpreorderのidealで、その性質がaに入っている。
      simp at a
      obtain ⟨hs, hhs⟩ := a --hsはsがVの要素であること。hhsは、sのidealとしての性質。
      use hs
      simp
      constructor
      · intro q hq q' hqq'
        obtain ⟨x, hx⟩ := Quotient.exists_rep q
        obtain ⟨x', hx'⟩ := Quotient.exists_rep q'

        --暗黙に使っているっぽい。
        have : s.V = (setup_setupspo s).V:= by
          exact rfl
        --使ってないのかも。
        --have :x'.val ∈ (setup_setupspo s).V := by
        --  subst hx hx'
        --  simp_all only [Subtype.forall, mem_filter, mem_attach, true_and, Subtype.exists, coe_mem]
        --have : x'.val ∈ s.V := by
        --  subst hx hx'
        --  simp_all only [Subtype.forall, mem_filter, mem_attach, true_and, Subtype.exists, coe_mem]
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
          exact reach_leq2 s q' q hqq'
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
            --simp_all only [eq_mpr_eq_cast, cast_eq]
            apply And.intro
            · intro x h
              exact left_3 x h
            · intro q a a_1 b a_2
              --subst a_2
              apply right
              · exact a
              · congr


--証明すべき内容。
-- setup_spo2をtraceしたもののidealがidealとしてtraceしたものと一致すること。

/-
--今の所、使ってないのかも。似た定理をSetupを使って作っている。pullback_preorder_lemmaなど。
lemma preorder_partialorder_lemma_exists {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) [Preorder { x // x ∈ V }] (w v:Quotient (@setoid_preorder {x // x ∈ V} _))  :
  w ≤ v ↔ (∃ x y, w = Quotient.mk (@setoid_preorder {x // x ∈ V} _) x ∧ v = Quotient.mk (@setoid_preorder {x // x ∈ V} _) y ∧ x ≤ y) := by
  apply Iff.intro
  · intro h
    rcases Quotient.exists_rep w with ⟨x, rfl⟩
    rcases Quotient.exists_rep v with ⟨y, rfl⟩
    use x
    use y
    simp
    exact h
  · intro h
    simp_all only [exists_and_left, Subtype.exists]
    obtain ⟨w_1, h⟩ := h
    obtain ⟨w_2, h⟩ := h
    obtain ⟨left, right⟩ := h
    obtain ⟨w_3, h⟩ := right
    obtain ⟨w_4, h⟩ := h
    obtain ⟨left_1, right⟩ := h
    subst left left_1
    exact right

--今の所、使ってないのかも。
lemma preorder_partialorder_lemma_all {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) [Preorder { x // x ∈ V }] (w v:Quotient (@setoid_preorder {x // x ∈ V} _))  :
  w ≤ v ↔ (∀ x y, w = Quotient.mk (@setoid_preorder {x // x ∈ V} _) x → v = Quotient.mk (@setoid_preorder {x // x ∈ V} _) y →x ≤ y) := by
  apply Iff.intro
  · intro h
    rcases Quotient.exists_rep w with ⟨x, hx⟩
    rcases Quotient.exists_rep v with ⟨y, hy⟩
    intro xx yy hxx hyy
    dsimp [setoid_preorder] at h
    rw [hxx, hyy] at h
    exact h
  · intro h
    rcases Quotient.exists_rep w with ⟨x, hx⟩
    rcases Quotient.exists_rep v with ⟨y, hy⟩
    subst hx hy
    simp_all only [Quotient.eq, AntisymmRel.setoid_r, Subtype.forall]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    apply h
    · rfl
    · rfl
-/
--noncomputable def preorder_ideal_system {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) [Preorder { x // x ∈ V }] (nonemp:V.Nonempty): ClosureSystem α :=
