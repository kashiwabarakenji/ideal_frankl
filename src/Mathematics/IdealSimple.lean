import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathematics.BasicDefinitions
import Mathematics.BasicLemmas
import LeanCopilot

namespace Mathematics

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

def domain00 (F : SetFamily α) (v : α) [DecidablePred F.sets] : Finset (Finset α) :=
  (Finset.powerset F.ground).filter (λ s => F.sets s ∧ v ∈ s)

theorem card_le_of_singletons_in_family [Fintype α] (F : SetFamily α) [DecidablePred F.sets]
  (hF : ∀ x : α, x ∈ F.ground → F.sets ({x})) :
  F.ground.card ≤ ((Finset.powerset F.ground).filter F.sets).card :=
by
  -- 関数 f : F.ground → Finset α を定義し、各要素 x を単一集合 {x} に写す
  -- 各要素 x を単一集合 {x} に対応させる関数 f を定義
  let f : {x // x ∈ F.ground} → (Finset.powerset F.ground).filter F.sets := λ x => ⟨{x.val},
    by
      simp [Finset.mem_filter, Finset.mem_powerset]
      rename_i inst inst_1 inst_2 inst_3 inst_4
      simp_all only [Finset.coe_mem]
    ⟩

  --let f : F.ground → Finset F.ground:= λ x => {x}
  -- 単射であることを示す
  have hf : Function.Injective f := by
    intros x y hxy
    dsimp [f] at hxy
    simp [Finset.ext_iff] at hxy
    exact Subtype.eq hxy
    -- 単射を使って F.ground.card ≤ フィルタリングされた集合の要素数を示す
  -- Finset 上の injective に基づく証明
  have hF_card : F.ground.card = F.ground.attach.card := by
    rw [Finset.card_attach]

  -- Powerset において単一集合 {x} が含まれていることを確認
  have hF_filter : ∀ x : {x // x ∈ F.ground}, {x.val} ∈ (Finset.powerset F.ground).filter F.sets :=
    by
      intro x
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff, true_and]
      simp [hF]

    -- Finset.card_le_of_injective を使って単射性に基づいてカードの不等式を示す
  have lq0 : F.ground.attach.card ≤ Fintype.card { x // x ∈ Finset.filter F.sets F.ground.powerset }:=
    by
      exact Fintype.card_le_of_injective f hf
      --Fintype.card_le_of_injective f hf : Fintype.card { x // x ∈ F.ground } ≤ Fintype.card (Finset α)
      -- @Fintype.card_le_of_injective : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β),
      -- Function.Injective f → Fintype.card α ≤ Fintype.card β

  have eq_card: ((Finset.powerset F.ground).filter F.sets).card = Fintype.card { x // x ∈ Finset.filter F.sets F.ground.powerset }:=
    by
      --#check Fintype.card_congr
      rw [Finset.card_filter]
      simp only [Finset.sum_ite, if_true]
      simp
      rw [Finset.card_filter]
      simp_rw [Finset.sum_boole]



      --apply Fintype.card_congr (λ x => x)
      --rw [←hF_card]
      rw [←Finset.card_attach]
      --rw [←Finset.card_filter_eq]
