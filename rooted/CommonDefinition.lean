
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

variable {α : Type} [Fintype α] [DecidableEq α]

structure SetFamily (α : Type) where
  (ground : Finset α)
  (sets : Finset α → Prop)
  (inc_ground : ∀ s, sets s → s ⊆ ground)
  (nonempty_ground : ground.Nonempty)
  --[decidableSets : DecidablePred sets]
  --[fintype_ground : Fintype ground]

noncomputable def SetFamily.number_of_hyperedges  (F : SetFamily α) [DecidablePred F.sets]: Int :=
  Int.ofNat (Finset.card (Finset.filter (λ s => F.sets s ) (F.ground.powerset)))

noncomputable def SetFamily.degree (F : SetFamily α)[DecidablePred F.sets]: α → Int := λ v => Int.ofNat (Finset.filter (λ s => F.sets s ∧ v ∈ s) F.ground.powerset).card

def SetFamily.is_rare (F : SetFamily α) (v : α)  [DecidablePred F.sets]  : Prop :=
  2 * F.degree v - F.number_of_hyperedges <= 0

noncomputable def SetFamily.total_size_of_hyperedges (F : SetFamily α) [DecidablePred F.sets] : Int :=
  Int.ofNat  (((Finset.powerset F.ground).filter F.sets).sum Finset.card)

noncomputable def SetFamily.normalized_degree {α : Type} [DecidableEq α]  (F : SetFamily α) [DecidablePred F.sets] (x: α): ℤ :=
  2 * (F.degree x:Int) - (F.number_of_hyperedges:Int)

noncomputable def SetFamily.normalized_degree_sum {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) [DecidablePred F.sets]: ℤ :=
  2 * (F.total_size_of_hyperedges:Int) - (F.number_of_hyperedges:Int)*(F.ground.card:Int)


@[ext]
structure ClosureSystem (α : Type) [DecidableEq α]  [Fintype α] extends SetFamily α where
  (intersection_closed : ∀ s t , sets s → sets t → sets (s ∩ t))
  (has_ground : sets ground)

def ClosureSystem.has_empty (α : Type) [DecidableEq α] [Fintype α] (S : ClosureSystem α) : Prop := S.sets ∅
