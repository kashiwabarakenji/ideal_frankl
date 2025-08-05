import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
--import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.functionalPartialMaximal
import rooted.functionalPartial

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

--This file is about traces of the maximal elements of a partially ordered set.The number of connected components is not necessarily 1.

--It's simpler than just a Setup.There is no need to consider the equivalent class as in preorder.
--structure Setup_po (α : Type) [Fintype α] [DecidableEq α] where
--(V : Finset α)
--(nonemp   : V.Nonempty)
--(f : V → V)
--(po : PartialOrder V)
--(order : ∀ x y : V, (reach f x y ↔ po.le x y))

--def reach {A : Type} (f : A → A) (x y : A) : Prop :=  ∃ n : ℕ, f^[n] x = y


--Trace of the max element in the semi-order.Used with PartialOne.
def po_trace (s : Setup_po α) (x : s.V)
    (pm   : po_maximal s x)
    (geq2 : s.V.card ≥ 2) : Setup_po α := by
  classical

  let V' : Finset α := s.V.erase x

  have nonemp' : (V' : Finset α).Nonempty := by
    have : (s.V.filter fun a : α => a ≠ x).card ≥ 1 := by
      have hcard := (show 2 ≤ s.V.card from geq2)
      have hx : (x : α) ∈ s.V := x.property
      have h₁ := (s.V.card_erase_add_one hx).symm
      have : (s.V.erase (x : α)).card + 1 = s.V.card := by
        simpa using s.V.card_erase_add_one hx
      have geq1: (s.V.erase (x : α)).card ≥ 1 := by
        have h₀ : s.V.card ≥ 2 := geq2
        have h₁ : (s.V.erase (x : α)).card + 1 = s.V.card :=
          s.V.card_erase_add_one hx
        linarith
      simp [V']
      apply Finset.card_pos.mp
      have :(filter (fun a => ¬a = ↑x) s.V) = s.V.erase ↑x := by
        ext a
        constructor
        · intro ha;
          rw [Finset.mem_erase]
          rw [Finset.mem_filter] at ha
          constructor
          · exact ha.2
          · exact ha.1
        · intro ha;
          rw [Finset.mem_erase] at ha
          rw [Finset.mem_filter]
          constructor
          · exact ha.2
          · exact ha.1
      have :#(filter (fun a => ¬a = ↑x) s.V) ≥ 1 := by
        rw [this]
        exact geq1
      exact this

    simp_all [V']
    obtain ⟨val, property⟩ := x
    simp_all only
    contrapose! this
    simp_all only [not_nontrivial_iff, ne_eq, Finset.not_nonempty_iff_eq_empty]
    ext a : 1
    simp_all only [mem_filter, Finset.notMem_empty, iff_false, not_and, Decidable.not_not]
    intro a_1
    apply this
    · simp_all only [mem_coe]
    · simp_all only [mem_coe]

  let φ : V' → s.V := fun y =>
    ⟨(y : α), (Finset.mem_of_mem_erase y.property)⟩

  have φ_inv : ∀ {z : s.V}, (z : α) ≠ x → (z : α) ∈ V' := by
    intro z hz
    have hzV : (z : α) ∈ s.V := z.property
    exact Finset.mem_erase.mpr ⟨hz, hzV⟩

  let f' : V' → V' := fun y => by

    let z : s.V := s.f (φ y)
    by_cases h : ((z : α) = x)

    · exact ⟨y, y.property⟩

    · exact ⟨(z : α), φ_inv (by simpa using h)⟩

  let le' : V' → V' → Prop := fun a b => s.po.le (φ a) (φ b)

  let po' : PartialOrder V' :=
  { le := le'
    le_refl := by
      intro a; exact s.po.le_refl _
    le_trans := by
      intro a b c h₁ h₂;
      exact s.po.le_trans _ _ _ (by simpa using h₁) (by simpa using h₂)

    le_antisymm := by
      intro a b h₁ h₂
      cases a with | mk a ha' =>
      cases b with | mk b hb' =>
      dsimp [le'] at h₁ h₂
      have ha: (a : α) ∈ s.V := by
        exact mem_of_mem_erase ha'
      have hb: (b : α) ∈ s.V := by
        exact mem_of_mem_erase hb'
      have : φ ⟨a, ha'⟩ = φ ⟨b, hb'⟩ := by
        apply s.po.le_antisymm ⟨a, ha⟩ ⟨b, hb⟩
        exact h₁
        exact h₂

      simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.mk.injEq, le', V', φ]
  }

  have order' : ∀ y z : V', reach f' y z ↔ po'.le y z := by
    intro y z

    have forward : reach f' y z → le' y z := by
      rintro ⟨n, hn⟩
      have step : ∀ a : V', le' a (f' a) := by
        intro a
        dsimp [le', f']
        by_cases h : s.f (φ a) = x
        · simp [h]
        · have : reach s.f (φ a) (s.f (φ a)) := ⟨1, by
            simp [Function.iterate_one]⟩
          have : s.po.le (φ a) (s.f (φ a))   :=
            (s.order _ _).1 this
          subst hn
          simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, f', le', V', φ]
          obtain ⟨val_1, property_1⟩ := y
          simp_all only [mem_erase, ne_eq, V']
          obtain ⟨left, right⟩ := property_1
          split
          next h_1 => simp_all only [le_refl]
          next h_1 => simp_all only [Subtype.coe_eta]

      have y_le_iter : ∀ k : ℕ, le' y (f'^[k] y) := by
        intro k
        induction k with
        | zero => exact s.po.le_refl (φ y)
        | succ k ih =>
          have : le' (f'^[k] y) (f'^[k + 1] y) :=
          by
            rw [Function.iterate_succ']
            exact step (f'^[k] y)
          exact s.po.le_trans _ _ _ ih this
      have : le' y (f'^[n] y) := y_le_iter n
      rwa [hn] at this

    have backward : le' y z → reach f' y z := by
      intro hle
      have : reach s.f (φ y) (φ z) := (s.order _ _).2 hle
      rcases this with ⟨n, hn⟩

      have φ_iter : ∀ m ≤ n, s.f^[m] (φ y) = φ (f'^[m] y) := by
        intro m hm
        induction m with
        | zero => simp
        | succ m ih =>
          have m_le_n : m ≤ n := Nat.le_of_succ_le hm
          have ih' := ih m_le_n
          rw [Function.iterate_succ', Function.iterate_succ']
          have not_x : s.f (φ (f'^[m] y)) ≠ x := by
            intro h
            have stuck_at_x : ∀ k ≥ m + 1, s.f^[k] (φ y) = x := by
              intro k hk
              induction k with
              | zero => simp at hk
              | succ k ihk =>
                if hk' : k ≥ m + 1 then
                  let ihkh := ihk hk'
                  have : s.f x = x := by
                    rw [po_maximal_lem] at pm
                    exact pm
                  rw [Function.iterate_succ']
                  rw [Function.comp_apply]
                  rw [ihkh]
                  exact this
                else
                  have : k = m := by linarith
                  subst this
                  rw [Function.iterate_succ']
                  simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, forall_const, IsEmpty.forall_iff, le_refl,
                    add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, not_false_eq_true, Function.comp_apply, f', le', V', φ]

            have : s.f^[n] (φ y) = x := stuck_at_x n (by linarith)

            rw [hn] at this
            have : (z : α) = x := Subtype.ext_iff.mp this
            have : z.val ∈ V' := z.property
            simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, forall_const, mem_erase, ne_eq,
              not_true_eq_false, and_true, f', le', V', φ]

          rw [Function.comp_apply,Function.comp_apply]
          rw [ih']
          -- goal: s.f (φ (f'^[m] y)) = φ (f' (f'^[m] y))
          have : φ (f' (f'^[m] y)) = s.f (φ (f'^[m] y)) := by
            dsimp [f']
            have hnot: s.f (φ (f'^[m] y)) ≠ x := not_x
            split_ifs with h
            · simp
              exfalso
              apply hnot
              exact Eq.symm (Subtype.eq (id (Eq.symm h)))
            · rfl
          exact this.symm



      have : f'^[n] y = z := by
        apply Subtype.ext
        suffices φ (f'^[n] y) = φ z from by
          simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, Subtype.mk.injEq, f', le', V', φ]
        let it := φ_iter n (le_refl n)
        rw [←it]
        exact hn

      exact ⟨n, this⟩

    show reach f' y z ↔ y ≤ z

    have po_le_eq_le' : po'.le = le' := by
        dsimp [po']

    simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, f', le', V', φ]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    obtain ⟨val_2, property_2⟩ := z
    simp_all only [V']
    apply Iff.intro
    · intro a
      simp_all only [forall_const, imp_self]
    · intro a
      simp_all only [imp_self, forall_const]

  exact
  { V      := V'
    nonemp := nonemp'
    f      := f'
    po     := po'
    order  := order' }
