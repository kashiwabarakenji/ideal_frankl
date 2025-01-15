import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Basic
import LeanCopilot

-- 有限集合の型
variable {α : Type} [Fintype α] [DecidableEq α]

structure SetFamily (α : Type) where --[DecidableEq α]  where DecidableEqをつけると、別のところで、synthesized type classエラー
  (ground : Finset α)
  (sets : Finset α → Prop)
  (inc_ground : ∀ s, sets s → s ⊆ ground)
  (nonempty_ground : ground.Nonempty)
  --[fintype_ground : Fintype ground]

--instance (SF : SetFamily α) : DecidablePred SF.sets :=
--  classical.dec_pred _

-- ValidPair の定義: ステム A と根 a
structure ValidPair  (α : Type) where
  stem : Finset α
  root : α
  h : root ∉ stem  -- a が A に含まれない条件

-- RootedSets の定義
structure RootedSets (α : Type) [DecidableEq α] where
  ground : Finset α
  rootedsets : Finset (ValidPair α)
  inc_ground : ∀ p ∈ rootedsets, p.stem ⊆ ground ∧ p.root ∈ ground
  nonempty_ground : ground.Nonempty
  [fintype_ground : Fintype ground]

-- フィルタされた通常の集合族の定義。SetFamilyに飛ばすように変更した方が良い。
noncomputable def filteredFamily (RS : RootedSets α):
  Finset (Finset α):=
RS.ground.powerset.filter (λ B =>
    ∀ (p : ValidPair α), p ∈ RS.rootedsets → ¬(p.stem ⊆ B ∧ p.root ∉ B))

noncomputable def filteredSetFamily (RS : RootedSets α):
  SetFamily α :=
{
  ground := RS.ground
  sets := fun s => s ∈ filteredFamily RS
  inc_ground :=
  by
    intro s a
    rw [filteredFamily] at a
    simp_all only [not_and, Decidable.not_not, Finset.mem_filter, Finset.mem_powerset]
  nonempty_ground := by
    obtain ⟨x, hx⟩ := RS
    simp_all only
}

-- RootedCircuits の定義
structure RootedCircuits (α : Type) [DecidableEq α] extends RootedSets α where
  minimality :
    ∀ p₁ p₂:(ValidPair α), p₁ ∈ rootedsets → p₂ ∈ rootedsets →
      p₁.root = p₂.root → p₁.stem ⊆ p₂.stem → p₁.stem = p₂.stem

def rootedcircuits_from_RS (RS : RootedSets α) : RootedCircuits α :=
{
  ground := RS.ground
  rootedsets:= RS.rootedsets.filter (λ p => ∀ q ∈ RS.rootedsets, q.root = p.root → ¬(q.stem ⊂ p.stem))
  inc_ground :=
  by
    intro p a
    simp_all only [Finset.mem_filter]
    obtain ⟨left, right⟩ := a
    apply And.intro
    · exact (RS.inc_ground p left).1
    · exact (RS.inc_ground p left).2

  minimality :=
  by
    intro p₁ p₂ hp₁ hp₂
    intro hroot hsubset
    simp only [Finset.mem_filter] at hp₁ hp₂
    -- `hp₁` と `hp₂` のフィルタ条件を取得
    obtain ⟨hp₁_in_RS, hp₁_min⟩ := hp₁
    obtain ⟨hp₂_in_RS, hp₂_min⟩ := hp₂
    -- `p₁.stem ⊆ p₂.stem` を仮定している
    by_contra hneq
    -- 仮定により `p₁.stem ⊂ p₂.stem` を導出 なぜか、定理が見つからない。
    have {s t : Finset α} :  s ⊆ t → s ≠ t → s ⊂ t :=
    by
      intro st snt
      apply Finset.ssubset_def.mpr
      constructor
      exact st
      by_contra hcontra
      let tmp := Finset.Subset.antisymm st hcontra
      contradiction

    have hproper : p₁.stem ⊂ p₂.stem :=
    by
      exact this hsubset hneq

    simp_all only [ne_eq]

  nonempty_ground := by
    obtain ⟨x, hx⟩ := RS
    simp_all only
}

omit [Fintype α] in
theorem filteredFamily_closed_under_intersection (RS : RootedSets α) [DecidablePred rootedsets]:
  ∀ B₁ B₂ : Finset α, B₁ ∈ filteredFamily RS → B₂ ∈ filteredFamily RS → (B₁ ∩ B₂) ∈ filteredFamily RS :=
by
  intros B₁ B₂ hB₁ hB₂
  simp only [filteredFamily, Finset.mem_filter] at hB₁ hB₂ ⊢
  obtain ⟨hB₁sub, hB₁cond⟩ := hB₁
  obtain ⟨hB₂sub, hB₂cond⟩ := hB₂
  have hInterSub : B₁ ∩ B₂ ⊆ RS.ground :=
  by
    simp_all only [Finset.mem_powerset, not_and, Decidable.not_not]
    intro p hp
    simp_all only [Finset.mem_inter]
    obtain ⟨left, right⟩ := hp
    exact hB₂sub right
  constructor
  simp_all only [Finset.mem_powerset, not_and, Decidable.not_not]

  intro p hp
  specialize hB₁cond p hp
  specialize hB₂cond p hp
  by_contra hContr
  simp only [Finset.subset_inter_iff, not_and, not_not] at hContr
  simp_all only [Finset.mem_powerset, true_and, Decidable.not_not, Finset.mem_inter, and_self, not_true_eq_false,
    and_false]

-- SetFamily から RootedSets を構築する関数
def rootedSetsFromSetFamily (SF : SetFamily α) [DecidableEq α] [DecidablePred SF.sets][Fintype SF.ground] : RootedSets α :=
  {
    ground := SF.ground
    rootedsets :=
      by
        -- Step 1: SF.ground の部分集合 (powerset) を生成
        let all_stems := SF.ground.powerset

        -- Step 2-1: root のフィルタ条件を定義
        let is_valid_root := λ root stem =>
          root ∉ stem ∧ ∀ s, SF.sets s → (s ⊆ stem → root ∈ s)
          --root ∉ stem ∧ ∀ (s:Finset α), (s ⊆ stem → root ∈ s)

        -- Step 2-2: stem ごとに root をフィルタリング
                -- Step 2-2: stem ごとに root をフィルタリング
        let filter_roots_for_stem := λ stem =>
          SF.ground.filter (λ root => is_valid_root root stem)

        -- Step 3: stem と root のペアを ValidPair に変換
        let make_pairs_for_stem := λ stem =>
          let valid_roots := filter_roots_for_stem stem
          valid_roots.map (λ root => ⟨stem, root, by simp [root]⟩)

        -- Step 4: すべての stem についてペアを生成
        let valid_pairs :=
          all_stems.filterMap (λ stem =>
            let pairs := make_pairs_for_stem stem
            if pairs.nonempty then some pairs else none)

        -- Step 5: ペアを結合して最終結果を生成
        exact valid_pairs.toFinset.bind id,

    inc_ground := by
      intros p hp
      simp only [Finset.mem_filterMap, Finset.mem_powerset] at hp
      obtain ⟨stem, hstem, root, hroot, p_eq⟩ := hp
      subst p_eq
      exact ⟨hstem, by simp at hroot; exact hroot.1⟩,
    nonempty_ground := SF.nonempty_ground
  }
