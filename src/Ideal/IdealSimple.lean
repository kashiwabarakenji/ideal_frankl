import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.Subtype
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import LeanCopilot

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

--singletonがすべてhyperedgeであれば、台集合の要素数は、その台集合の冪集合の中でhyperedgeであるものの要素数以下である

-- 下で使っている。
lemma card_lemma {α : Type} [Fintype α] [DecidableEq α] (A : Finset α) (P : α → Prop) [DecidablePred P] :
  (A.filter P).card = Fintype.card { x // x ∈ A ∧ P x } :=
by
  -- フィルタリングされた Finset を定義
  set filtered := A.filter P with hfiltered

  -- Fintype インスタンスを作成
  have : Fintype { x // x ∈ A ∧ P x } :=
    Fintype.ofFinset filtered (λ x => (by
    apply Iff.intro
    · intro a
      simp_all only [Finset.mem_filter, filtered]
      obtain ⟨left, right⟩ := a
      exact ⟨left, right⟩
    · intro a
      simp_all only [Finset.mem_filter, filtered]
      exact a))

  -- apply Fintype.card_of_subtype を使ってゴールを作る
  have H: ∀ (x : α), x ∈ filtered ↔ x ∈ A ∧ P x := by
    intro x
    simp only [Finset.mem_filter, filtered]

  have H2 : Fintype.card { x // x ∈ A ∧ P x } = filtered.card :=
    (Fintype.card_of_subtype filtered H)
  --Fintype.card_of_subtype filtered H : Fintype.card { x // x ∈ A ∧ P x } = filtered.card
  rw [hfiltered] at H2
  symm
  simp_all only [Finset.mem_filter, implies_true, filtered]
  convert H2

-- 任意の x ∈ F.ground に対して、{x} が hyperedgeと仮定すると、台集合の大きさは、hyperedge数以下である。
--使ってない。
omit [Nonempty α] in
theorem card_le_of_singletons_in_family  (F : SetFamily α) [DecidablePred F.sets]
  (hF : ∀ x : α, x ∈ F.ground → F.sets ({x})) :
  F.ground.card ≤ ((Finset.powerset F.ground).filter F.sets).card :=
by
  -- 関数 f : F.ground → Finset α を定義し、各要素 x を単一集合 {x} に写す
  -- 各要素 x を単一集合 {x} に対応させる関数 f を定義
  let f : {x // x ∈ F.ground} → (Finset.powerset F.ground).filter F.sets := λ x => ⟨{x.val},
    by
      simp [Finset.mem_filter, Finset.mem_powerset]
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
  /-
  -- Finset 上の injective に基づく証明
  have hF_card : F.ground.card = F.ground.attach.card := by
    rw [Finset.card_attach]

  -- Powerset において単一集合 {x} が含まれていることを確認
  have hF_filter : ∀ x : {x // x ∈ F.ground}, {x.val} ∈ (Finset.powerset F.ground).filter F.sets :=
    by
      intro x
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff, true_and]
      simp [hF]
  -/

  -- Finset.card_le_of_injective を使って単射性に基づいてカードの不等式を示す。最後のsimp_allで暗黙に使っているみたい。
  have lq0 : F.ground.attach.card ≤ Fintype.card { x // x ∈ Finset.filter F.sets F.ground.powerset }:=
    by
      exact Fintype.card_le_of_injective f hf
      --Fintype.card_le_of_injective f hf : Fintype.card { x // x ∈ F.ground } ≤ Fintype.card (Finset α)
      -- @Fintype.card_le_of_injective : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β),
      -- Function.Injective f → Fintype.card α ≤ Fintype.card β

  have H: ((Finset.powerset F.ground).filter F.sets).card = Fintype.card { x // x ∈ Finset.filter F.sets F.ground.powerset }  :=
    by
      let cl := card_lemma F.ground.powerset F.sets
      simp_all

  simp_all only [Finset.card_attach, Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff,
    Finset.coe_mem, and_self, implies_true, f]

------
