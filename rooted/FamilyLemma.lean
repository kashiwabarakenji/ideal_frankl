import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Finprod
import rooted.CommonDefinition

open Classical

variable {α : Type} [Fintype α] [DecidableEq α]

--lean 4.16 lacked the import Mathlib.Algebra.BigOperators.Ring.Finset library.
--Revived on 4/17.It affects sum_boole, etc.It's difficult to prove without it.
--It is necessary to support set family instead of --closure system.
--The interface for the whole set is the following theorem.
omit [Fintype α] in
lemma double_counting_lemma_X (SF:SetFamily α) [DecidablePred SF.sets] (X: Finset α) :
  ∑ s ∈ (SF.ground.powerset.filter SF.sets), (X ∩ s).card = ∑ v ∈ X,SF.degree v :=
by
  dsimp [SetFamily.degree]

--hyperedge The difference between the number of s and vertex v, where v∈ s holds, or the sum of v is calculated first, or the sum of v is calculated first.
--The above lemma cannot be applied directly.It's not s.card, but (s ∩ X).card.
  let S := Finset.filter SF.sets SF.ground.powerset
  have : ∑ s ∈ S, (X ∩ s).card
       = ∑ s ∈ S, ∑ v ∈ X, if v ∈ s then 1 else 0 := by
    congr with s
    -- (X ∩ s).card を ∑ v in X, if v ∈ s then 1 else 0 で書き換え
    rw [Finset.card_eq_sum_ones, Finset.sum_boole]
    simp_all only [Finset.sum_const, smul_eq_mul, mul_one, Nat.cast_id]
    rfl
  -- Exchange sum order using the above equation
  rw [this, Finset.sum_comm]
  -- Rewrite the inner sum: ∑ s in S, if v ∈ s then 1 else 0 = (filter (λ s, v ∈ s) S).card

  rw [Finset.sum_congr rfl]
  symm
  norm_cast

  intro x a
  simp_all only [Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_boole, Nat.cast_id, S]
  congr 1
  rw [Finset.filter_filter]

--Prove double counting lemma on the whole set.
omit [Fintype α] in
lemma double_counting_lemma (SF:SetFamily α) [DecidablePred SF.sets]:
  ∑ s ∈ (SF.ground.powerset.filter SF.sets), s.card = ∑ v ∈ SF.ground,SF.degree v :=
by
  let dcl := double_counting_lemma_X SF SF.ground
  rw [←dcl]
  simp
  apply Finset.sum_congr rfl
  intro s hs
  let ig := SF.inc_ground s
  have :  SF.sets s := by
    rw [Finset.mem_filter] at hs
    exact hs.right
  specialize ig this
  have :SF.ground ∩ s = s :=
  by
    exact Finset.inter_eq_right.mpr ig
  rw [this]
