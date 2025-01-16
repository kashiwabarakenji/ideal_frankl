import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Finset.Union
import LeanCopilot

-- 有限集合の型
variable {α : Type} [Fintype α] [DecidableEq α]

open Classical  --これでsetsのdecidablePredの問題が解決した。

structure SetFamily (α : Type) where --[DecidableEq α]  where DecidableEqをつけると、別のところで、synthesized type classエラー
  (ground : Finset α)
  (sets : Finset α → Prop)
  (inc_ground : ∀ s, sets s → s ⊆ ground)
  (nonempty_ground : ground.Nonempty)
  --[decidableSets : DecidablePred sets]
  --[fintype_ground : Fintype ground]


--instance (SF : SetFamily α) : DecidablePred SF.sets :=
--  classical.dec_pred _

-- ValidPair の定義: ステム A と根 a
structure ValidPair (α : Type) where
  stem : Finset α
  root : α
  root_not_in_stem : root ∉ stem

structure RootedSets (α : Type) [DecidableEq α] where
  ground : Finset α
  rootedsets : Finset (ValidPair α)
  inc_ground : ∀ p ∈ rootedsets, p.stem ⊆ ground ∧ p.root ∈ ground
  nonempty_ground : ground.Nonempty

 -- [fintype_ground : Fintype ground]

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

def Finset.apply_function_to_subtype {α β : Type*} [DecidableEq β] {p : α → Prop}
    (s : Finset {x // p x}) (f : α → β) : Finset β :=
  s.image (λ x => f x.val)

-- SetFamily から RootedSets を構築する関数 noncomputableはつけた方がいいのか。
noncomputable def rootedSetsFromSetFamily (SF : SetFamily α) [DecidableEq α] [DecidablePred SF.sets][Fintype SF.ground] : RootedSets α :=
  {
    ground := SF.ground
    rootedsets := by

    -- Step 1: ground のすべての部分集合 (powerset) を列挙
      let all_stems := SF.ground.powerset

      -- Step 2: 各 stem に対し、有効な root をフィルタ
      --   条件: root ∉ stem ∧ ∀ s, SF.sets s → (s ⊆ stem → root ∈ s)

      let filter_roots_for_stem := λ (stem : Finset α) =>
        SF.ground.filter (λ root =>
          root ∉ stem
          ∧ ∀ s, SF.sets s → (s ⊆ stem → root ∈ s)
        )
      -- Step 3: stem と root を組み合わせて ValidPair を作る
      --
      --   ただし、Finset.image のラムダ式内では「r が valid_roots に属している」
      --   という事実を tactic mode で直接使いにくいので、Finset.attach を用いる
      --
      --   valid_roots.attach は、各 r ∈ valid_roots を 「⟨r, (r ∈ valid_roots) の証拠⟩」
      --   という形に変換するので、その証拠を取り出して root_not_in_stem を証明できる
      let make_pairs_for_stem0 := λ (stem : Finset α) =>
        let valid_roots := filter_roots_for_stem stem
        valid_roots.image (fun r => (stem,r))

      have rs_relation: ∀ (stem : Finset α) (r : α), (stem,r) ∈ make_pairs_for_stem0 stem → r ∉ stem :=
      by
        intros stem r
        intro a
        simp_all only [Finset.mem_image, Finset.mem_filter, Prod.mk.injEq, true_and, exists_eq_right,
          not_false_eq_true, make_pairs_for_stem0, filter_roots_for_stem]

      let allValidPairs := all_stems.attach.biUnion (λ stem =>
        let pairs := make_pairs_for_stem0 stem.val
        if pairs.Nonempty then pairs else ∅
      )

      let make_pairs_for_stem := allValidPairs.image (λ vp =>
        ValidPair.mk vp.1 vp.2 (rs_relation vp.1 vp.2 (by
        have: (vp.1,vp.2) ∈ make_pairs_for_stem0 vp.1 := by
          dsimp [make_pairs_for_stem0]
          dsimp [filter_roots_for_stem]
          simp
          use vp.2
          constructor
          constructor
          sorry --証明可能
          constructor
          sorry --難しい
          sorry --よくわからない。
          simp_all only [Finset.mem_image, Finset.mem_filter, Prod.mk.injEq, true_and, exists_eq_right,
            not_false_eq_true, implies_true, Prod.mk.eta, make_pairs_for_stem0, filter_roots_for_stem]
        simp_all only [Finset.mem_image, Finset.mem_filter, Prod.mk.injEq, true_and, exists_eq_right,
          not_false_eq_true, implies_true, Prod.mk.eta, make_pairs_for_stem0, filter_roots_for_stem]

        ----------------------------------------------------------------
      -- Step 4: すべての stem についてペアの集合を作り、それを biUnion で結合
      --
      --   if pairs.Nonempty then pairs else ∅
      --   にしているのは、空の場合を除外するためのサンプル処理
      ----------------------------------------------------------------
      let valid_pairs :=
        all_stems.biUnion (λ stem =>
          let pairs := make_pairs_for_stem stem
          if pairs.Nonempty then pairs else ∅
        )

      -- 最後に Finset (ValidPair α) を返す
      exact valid_pairs,

    /-
    rootedsets := by
      ----------------------------------------------------------------
      -- Step 1: stem (全体の台集合 ground の部分集合) を列挙
      ----------------------------------------------------------------
      let all_stems := SF.ground.powerset

      ----------------------------------------------------------------
      -- Step 2: stem ごとに root をフィルタリング
      ----------------------------------------------------------------
      let filter_roots_for_stem := λ (stem : Finset α) =>
        SF.ground.filter (λ root =>
          root ∉ stem
          ∧ ∀ s, SF.sets s → (s ⊆ stem → root ∈ s)
        )

      ----------------------------------------------------------------
      -- Step 3: stem と root のペア (ValidPair) を生成
      ----------------------------------------------------------------
      let make_pairs_for_stem := λ (stem : Finset α) =>
        let valid_roots := filter_roots_for_stem stem

        -- (1) 「valid_roots にいる root は全て root ∉ stem ∧ ∀ s, SF.sets s → ...」という補題
        have h_valid_roots : ∀ root ∈ valid_roots,
          root ∉ stem ∧ ∀ s, SF.sets s → (s ⊆ stem → root ∈ s) :=
        by
          -- r ∈ valid_roots = SF.ground.filter p
          -- から r ∈ SF.ground ∧ p(r) が出る
          intros r hr
          simp_all only [Finset.mem_filter, not_false_eq_true, implies_true, and_self, valid_roots,
            filter_roots_for_stem]

        -- (2) ValidPair にパッケージ化
        valid_roots.image (λ root =>
          ValidPair.mk stem root
            ( (h_valid_roots root (by
                -- ここでは「root ∈ valid_roots」だけ示せればOK
                -- つまり root ∈ SF.ground ∧ root ∉ stem ∧ ...
                dsimp only [valid_roots]
                dsimp [filter_roots_for_stem]
                rw [Finset.mem_filter]
                constructor
                simp_all only [Finset.mem_filter, not_false_eq_true, implies_true, and_self, valid_roots,
                  filter_roots_for_stem]
                sorry -- root ∉ stem ∧ ∀ s, ..

                simp_all only [Finset.mem_filter, not_false_eq_true, implies_true, and_self, valid_roots,
                  filter_roots_for_stem]
                apply And.intro
                · sorry --root ∉ stem

                · intro s a a_1
                  sorry
              )).1
            )
        )

      ----------------------------------------------------------------
      -- Step 4: 全ての stem に対してペアを作り、biUnion
      ----------------------------------------------------------------
      let valid_pairs :=
        all_stems.biUnion (λ (stem : Finset α) =>
          let pairs := make_pairs_for_stem stem
          if pairs.Nonempty then pairs else ∅
        )

      exact valid_pairs,
    -/

    inc_ground := by
      intros p hp
      simp only [Finset.mem_filterMap, Finset.mem_powerset] at hp
      obtain ⟨stem, hstem, hp⟩ := Finset.mem_biUnion.mp hp
      rename_i hp_1
      simp_all only [Finset.mem_biUnion, Finset.mem_powerset]
      obtain ⟨w, h⟩ := hp_1
      obtain ⟨left, right⟩ := h
      apply And.intro
      · split at hp
        next h =>
          split at right
          next h_1 => sorry
          next h_1 => simp_all only [Finset.not_nonempty_iff_eq_empty, Finset.not_mem_empty]
        next h =>
          split at right
          next h_1 => simp_all only [Finset.not_nonempty_iff_eq_empty, Finset.not_mem_empty]
          next h_1 => simp_all only [Finset.not_nonempty_iff_eq_empty, Finset.not_mem_empty]
      · split at hp
        next h =>
          split at right
          next h_1 => sorry
          next h_1 => simp_all only [Finset.not_nonempty_iff_eq_empty, Finset.not_mem_empty]
        next h =>
          split at right
          next h_1 => simp_all only [Finset.not_nonempty_iff_eq_empty, Finset.not_mem_empty]
          next h_1 => simp_all only [Finset.not_nonempty_iff_eq_empty, Finset.not_mem_empty]

    nonempty_ground := SF.nonempty_ground
  }
