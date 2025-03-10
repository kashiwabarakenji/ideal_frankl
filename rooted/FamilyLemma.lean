
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
/-
--Xに関するdouble counting lemmaも証明した方がいい？
lemma double_counting_lemma (SF:ClosureSystem α) [DecidablePred SF.sets] (X: Finset α) :
  Int.ofNat (∑ s ∈ (SF.ground.powerset.filter SF.sets), (X ∩ s).card) = ∑ v ∈ X,SF.degree v :=
by
  dsimp [SetFamily.degree]

  --hyperedge sと頂点vが、v∈ sが成り立つ個数についてsを先に和を計算するか、vの和を先に計算するかの違い。
  --上の補題を直接適用できない。s.cardでなくて、(s ∩ X).cardになっているので。
  let S := Finset.filter SF.sets SF.ground.powerset
  have : ∑ s ∈ S, (X ∩ s).card
       = ∑ s ∈ S, ∑ v ∈ X, if v ∈ s then 1 else 0 := by
    congr with s
    -- (X ∩ s).card を ∑ v in X, if v ∈ s then 1 else 0 で書き換え
    rw [Finset.card_eq_sum_ones]
    simp_all only [Finset.sum_const,  mul_one]
    simp only [Finset.sum_ite_mem]
    exact Eq.symm (Finset.sum_const 1)
  -- 上記の式を使って和の順序を交換
  rw [this, Finset.sum_comm]
  -- 内側の和を書き換え: ∑ s in S, if v ∈ s then 1 else 0 = (filter (λ s, v ∈ s) S).card
  norm_cast
  dsimp [S]

  have : (∑ y ∈ X, ∑ x ∈ Finset.filter SF.sets SF.ground.powerset, if y ∈ x then 1 else 0) =
   (∑ v ∈ X, (Finset.filter (fun s => SF.sets s ∧ v ∈ s) SF.ground.powerset).card) := by

    apply Finset.sum_congr rfl
    · intro v hv
      norm_cast
      simp_all only [Finset.sum_ite_mem, Finset.sum_const, mul_one, S]

      congr 1
      rw [Finset.card_eq_sum_ones]
      rw [Finset.sum_filter]
      rw [Finset.sum_filter]
      apply Finset.sum_congr  --ここで情報が落ちている。
      exact rfl

      intro x hx
      split
      case a.isTrue h0 =>
        split
        case isTrue h1 =>
          simp_all [h0, h1]
        case isFalse h1 =>
          simp_all [h0, h1]

      case a.isFalse h0 =>
        split
        case isTrue h1 =>
          simp_all [h0, h1]
        case isFalse h1 =>
          simp_all [h0, h1]
  rw [this]
 -/
  --lean 4.16ではimport Mathlib.Algebra.BigOperators.Ring.Finsetのライブラリが欠けていた。
  --4.17で復活した。sum_booleなどに影響。なしで証明するのは難しい。
  --closure systemでなく、set familyに対応させる必要がある。
  --全体集合用のinterfaceは次の定理。
omit [Fintype α] in
lemma double_counting_lemma_X (SF:SetFamily α) [DecidablePred SF.sets] (X: Finset α) :
  ∑ s ∈ (SF.ground.powerset.filter SF.sets), (X ∩ s).card = ∑ v ∈ X,SF.degree v :=
by
  dsimp [SetFamily.degree]

  --hyperedge sと頂点vが、v∈ sが成り立つ個数についてsを先に和を計算するか、vの和を先に計算するかの違い。
  --上の補題を直接適用できない。s.cardでなくて、(s ∩ X).cardになっているので。
  let S := Finset.filter SF.sets SF.ground.powerset
  have : ∑ s ∈ S, (X ∩ s).card
       = ∑ s ∈ S, ∑ v ∈ X, if v ∈ s then 1 else 0 := by
    congr with s
    -- (X ∩ s).card を ∑ v in X, if v ∈ s then 1 else 0 で書き換え
    rw [Finset.card_eq_sum_ones, Finset.sum_boole]
    simp_all only [Finset.sum_const, smul_eq_mul, mul_one, Nat.cast_id]
    rfl
  -- 上記の式を使って和の順序を交換
  rw [this, Finset.sum_comm]
  -- 内側の和を書き換え: ∑ s in S, if v ∈ s then 1 else 0 = (filter (λ s, v ∈ s) S).card

  rw [Finset.sum_congr rfl]
  symm
  norm_cast

  intro x a
  simp_all only [Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_boole, Nat.cast_id, S]
  congr 1
  rw [Finset.filter_filter]

--全体集合でdouble counting lemmaを証明する。
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
