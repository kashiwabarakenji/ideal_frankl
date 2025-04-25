import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Tactic
import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne
import rooted.functionalCommon
import rooted.functionalPreorder

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

lemma setup_nds (s:Setup α): (preorder_ideal_system s).normalized_degree_sum ≤ 0 :=
by
  sorry

theorem functional_family_average_rare (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty) :
  (rootedsetToClosureSystem (rootedset_onestem_eachvertex_V V f valid nonemp)).normalized_degree_sum ≤ 0 :=
by
  let rs := rootedset_onestem_eachvertex_V V f valid nonemp
  set pre := size_one_preorder V f valid nonemp with h_pre
  set st := @setoid_preorder V pre with h_st
  let s := Setup.mk V nonemp f valid pre h_pre st h_st
  let sns := setup_nds s
  --ndsを議論する前にpreorderidealsystemと(rootedsetToClosureSystem (rootedset_onestem_eachvertex_V V f valid nonemp))の関係の補題を作った方が良さそう。
  sorry





  let sun := setup_nds (rootedset_onestem_eachvertex_V V f valid nonemp)
