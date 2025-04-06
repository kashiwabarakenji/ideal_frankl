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

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

def reach {A : Type} (f : A → A) (x y : A) : Prop :=
  ∃ n : ℕ, f^[n] x = y

def partialOrderOfFq {A : Type} (f : A → A)
  (noLoop : ∀ x y, reach f x y → reach f y x → x = y)
  : PartialOrder A :=
{ le := reach f
  le_refl := by
    intro x
    dsimp [reach]
    use 0
    simp_all only [Function.iterate_zero, id_eq]

  le_trans := by
      intro x y z ⟨n, hn⟩ ⟨m, hm⟩
      exists (n + m)
      subst hn hm
      unfold Nat.iterate
      induction n generalizing x with
      | zero => simp [Nat.iterate, Nat.zero_add]
      | succ n ih =>
        simp [Nat.iterate, Nat.succ_add, ih]
        apply noLoop
        dsimp [reach]
        split
        next x_1 x_2 =>
          simp_all only [add_zero]
          specialize ih x
          split at ih
          next x_3 x_4 =>
            simp_all only [Function.iterate_zero, id_eq]
            use 0
            exact rfl
          next x_3 x_4
            k =>
            simp_all only [Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply]
            use 0
            exact rfl
        next x_1 x_2 k =>
          simp_all only [Nat.add_eq, Nat.succ_eq_add_one]
          use 0
          simp
          specialize ih (f x)
          rw [←ih]
          simp_all only
          exact ih
        next x_1 x_2 =>
          dsimp [reach]
          specialize ih x
          split at ih
          · rename_i x1 x2 x3 x4
            simp_all only [AddLeftCancelMonoid.add_eq_zero, Function.iterate_zero, id_eq, add_zero]
            obtain ⟨left, right⟩ := x4
            subst right left
            exact ⟨0, by rw [Function.iterate_zero, id]⟩
          · rename_i x1 x2 x3 x4 x5
            simp_all only [Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply]
            search_proof










      sorry
      dsimp [iterate] at *
      -- iterate f n x = y, iterate f m y = z ⇒ iterate f (n+m) x = z
      -- これは簡単な再帰的補題で証明できる
      -- あるいは Mathlib.Data.Nat.Basic にある補題を使ってもOK
      -- 簡単のため直接書く
      induction n generalizing x with
      | zero => exact hm
      | succ n ih =>
        rw [iterate, hn]
        apply ih
        assumption
  , le_antisymm := by
      intro x y hxy hyx
      exact noLoop x y hxy hyx
}

structure Setup_spo (α : Type) [Fintype α] [DecidableEq α] where
  (V : Finset α)
  (nonemp   : V.Nonempty)
  (setoid : Setoid {x : α // x ∈ V})
  (fq : Quotient setoid → Quotient setoid)
  (spo : PartialOrder (Quotient setoid))
  (le : ∀ x y : Quotient setoid, x ≤ y ↔

def isMaximal_spo (s: Setup_spo α) (x : Quotient s.setoid) : Prop :=
  ∀ y : Quotient s.setoid,
  s.spo.le x y → s.spo.le y x

def classOf (s : Setup_spo α) (q : Quotient s.setoid) [DecidableEq (Quotient s.setoid)]  : Finset {x // x ∈ s.V} :=
  Finset.filter (fun (a : {x // x ∈ s.V}) => @Quotient.mk'' _ s.setoid a = q) s.V.attach
