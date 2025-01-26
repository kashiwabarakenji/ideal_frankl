import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic

variable {α : Type} [Fintype α] [DecidableEq α]

structure SetFamily (α : Type) where --[DecidableEq α]  where DecidableEqをつけると、別のところで、synthesized type classエラー
  (ground : Finset α)
  (sets : Finset α → Prop)
  (inc_ground : ∀ s, sets s → s ⊆ ground)
  (nonempty_ground : ground.Nonempty)
  --[decidableSets : DecidablePred sets]
  --[fintype_ground : Fintype ground]
  --instance (SF : SetFamily α) : DecidablePred SF.sets :=
  --  classical.dec_pred _

noncomputable def SetFamily.number_of_hyperedges  (F : SetFamily α) [DecidablePred F.sets]: Int :=
  Int.ofNat (Finset.card (Finset.filter (λ s => F.sets s ) (F.ground.powerset)))

noncomputable def SetFamily.degree (F : SetFamily α)[DecidablePred F.sets]: α → Int := λ v => Int.ofNat (Finset.filter (λ s => F.sets s ∧ v ∈ s) F.ground.powerset).card


def SetFamily.is_rare (F : SetFamily α) (v : α)  [DecidablePred F.sets]  : Prop :=
  2 * F.degree v - F.number_of_hyperedges <= 0

--ClosureSystemの定義から空集合を分離した。
@[ext]
structure ClosureSystem (α : Type) [DecidableEq α]  [Fintype α] extends SetFamily α where
  (intersection_closed : ∀ s t , sets s → sets t → sets (s ∩ t))
  (has_ground : sets ground)

def ClosureSystem.has_empty (α : Type) [DecidableEq α] [Fintype α] (S : ClosureSystem α) : Prop := S.sets ∅
