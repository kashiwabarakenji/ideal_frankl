import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

structure SetFamily (α : Type) where --[DecidableEq α]  where DecidableEqをつけると、別のところで、synthesized type classエラー
  (ground : Finset α)
  (sets : Finset α → Prop)
  (inc_ground : ∀ s, sets s → s ⊆ ground)
  (nonempty_ground : ground.Nonempty)
  --[decidableSets : DecidablePred sets]
  --[fintype_ground : Fintype ground]
  --instance (SF : SetFamily α) : DecidablePred SF.sets :=
  --  classical.dec_pred _

--ClosureSystemの定義から空集合を分離した。
@[ext]
structure ClosureSystem (α : Type) [DecidableEq α]  [Fintype α] extends SetFamily α where
  (intersection_closed : ∀ s t , sets s → sets t → sets (s ∩ t))
  (has_ground : sets ground)

def ClosureSystem.has_empty (α : Type) [DecidableEq α] [Fintype α] (S : ClosureSystem α) : Prop := S.sets ∅
