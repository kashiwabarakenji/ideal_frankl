import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Quot
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

structure Setup_spo2 (α : Type) [Fintype α] [DecidableEq α]
  extends Setup_spo α where
  -- 極大でない要素の同値類のサイズが 1
  singleton_if_not_maximal :
  ∀ q : Quotient toSetup_spo.setoid,
    (classOf toSetup_spo q).card ≥ 2 →
    isMaximal_spo toSetup_spo q


def setup2_induces_spo (s : Setup2 α) : Setup_spo2 α :=
{
  V := s.V,
  nonemp := s.nonemp,
  setoid := s.setoid,
  fq := fq s
  noLoop := (setup_setupspo s).noLoop,
  spo := (setup_setupspo s).spo,
  h_spo := (setup_setupspo s).h_spo,
  singleton_if_not_maximal := by
    intro q hq
    dsimp [isMaximal_spo] at hq
    let csm := eqClass_Maximal s q hq
    dsimp [isMaximalQ] at csm
    dsimp [isMaximal_spo]
    intro y h
    specialize csm y
    dsimp [setup_setupspo] at h
    dsimp [partialOrderOfFq] at h
    have : s.po.le q y := by
      simp_all only [ge_iff_le]
      exact reach_leq2 s q y h
    specialize csm this

    rw [spole_iff_po] at csm
    exact csm
}
