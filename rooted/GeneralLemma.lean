import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import LeanCopilot

--open Finset

variable {α : Type} [DecidableEq α] [Fintype α]

omit [Fintype α]
lemma exists_one_elements_removed {A B : Finset α} (hBA : B ⊆ A) (hcard : B.card = A.card - 1) (geq1 :A.card ≥ 1):
  ∃ x :α , x ∈ A ∧ A \ {x} = B :=
by
  have h : (A \ B).card = 1 :=
  by
    rw [Finset.card_sdiff hBA, hcard]
    exact Nat.sub_sub_self geq1

  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h

  use x
  constructor
  · have : x ∈ A := (Finset.mem_sdiff.mp (hx.symm ▸ Finset.mem_singleton_self x)).1
    exact this
  · rw [←hx]
    simp
    exact hBA

lemma exists_two_elements_removed {A B : Finset α} (hBA : B ⊆ A) (hcard : B.card = A.card - 2) (geq2 :A.card ≥ 2):
  ∃ x y :α , x ∈ A ∧ y ∈ A ∧ A \ {x, y} = B :=
by
  -- `A \ B` の要素数が 2 であることを確認
  have h : (A \ B).card = 2 := by
    rw [Finset.card_sdiff hBA, hcard]
    exact Nat.sub_sub_self geq2

  obtain ⟨x, y, hx⟩ := Finset.card_eq_two.mp h

  use x, y
  have : {x,y}⊆ A :=
  by
    simp_all only [ge_iff_le, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
      Finset.card_singleton, Nat.reduceAdd, ne_eq]
    obtain ⟨left, right⟩ := hx
    simp [← right]
  constructor
  · -- x ∈ A
    have : x ∈ A :=
    by
       simp_all only [ge_iff_le, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
         Finset.card_singleton, Nat.reduceAdd, ne_eq]
       obtain ⟨left, right⟩ := hx
       apply this
       simp_all only [Finset.mem_insert, Finset.mem_singleton, or_false]
    exact this
  · constructor
    · have : y ∈ A :=
      by
        simp_all only [ge_iff_le, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
          Finset.card_singleton, Nat.reduceAdd, ne_eq]
        obtain ⟨left, right⟩ := hx
        apply this
        simp_all only [Finset.mem_insert, Finset.mem_singleton, or_true]
      exact this
    ·
      simp_all only [ge_iff_le, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
        Finset.card_singleton, Nat.reduceAdd, ne_eq]
      obtain ⟨left, right⟩ := hx
      rw [propext (sdiff_eq_comm hBA this)] at right
      exact right
