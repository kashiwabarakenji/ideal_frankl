--Ideal集合族が平均abundantにならないことの証明が目標。

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Tactic
import Mathematics.BasicDefinitions
import Mathematics.BasicLemmas
import LeanCopilot

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

lemma sum_partition_by_v (F : SetFamily α) (v : α) [DecidablePred F.sets] :
  total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ v ∈ s,
                                     inc_ground := λ s hs => F.inc_ground s (hs.1) } +
  total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ v ∉ s,
                                     inc_ground := λ s hs => F.inc_ground s (hs.1) } =
  total_size_of_hyperedges F :=
by
  rw [total_size_of_hyperedges, total_size_of_hyperedges, total_size_of_hyperedges]
  let Fv := (Finset.powerset F.ground).filter (λ s => F.sets s ∧ v ∈ s)
  let Fnv := (Finset.powerset F.ground).filter (λ s => F.sets s ∧ v ∉ s)
  let Fsets := (Finset.powerset F.ground).filter F.sets

  have disjoint_v : Fsets = Fv ∪ Fnv :=
    by
     ext; simp [Finset.mem_union, Finset.mem_filter];
     --rename_i inst inst_1 inst_2 inst_3 a
     simp_all only [Finset.mem_filter, Finset.mem_powerset, Fsets, Fv, Fnv]
     apply Iff.intro
     · intro a_1
       simp_all only [true_and]
       obtain ⟨_, right⟩ := a_1
       contrapose! right
       simp_all only [not_and_self]
     · intro a_1
       cases a_1 with
       | inl h => simp_all only [and_self]
       | inr h_1 => simp_all only [and_self]

  -- Use the sum_union lemma to split the sum over the union
  have union_card_sum : (Fv ∪ Fnv).sum Finset.card = Fv.sum Finset.card + Fnv.sum Finset.card :=
    Finset.sum_union (by
    --theorem Finset.sum_union {β : Type u}  {α : Type v}  {s₁ : Finset α}  {s₂ : Finset α}  {f : α → β}  [AddCommMonoid β]  [DecidableEq α] (h : Disjoint s₁ s₂) :
    --(Finset.sum (s₁ ∪ s₂) fun x => f x) = (Finset.sum s₁ fun x => f x) + Finset.sum s₂ fun x => f x
    --以下はdisjointの証明。
    --goal Disjoint (Finset.filter (fun s => F.sets s ∧ v ∈ s) F.ground.powerset) (Finset.filter (fun s => F.sets s ∧ v ∉ s) F.ground.powerset)
      simp_all only [Fsets, Fv, Fnv]
      rw [Finset.disjoint_left]
      --theorem Finset.disjoint_left {α : Type u_1}  {s : Finset α}  {t : Finset α} :Disjoint s t ↔ ∀ ⦃a : α⦄, a ∈ s → a ∉ t
      intro a a_1
      simp_all only [Finset.mem_filter, Finset.mem_powerset, not_true_eq_false, and_false, not_false_eq_true]
    )

  rw [←union_card_sum]
  rw [←disjoint_v]




lemma ground_nonempty_after_deletion {α : Type} [DecidableEq α] (ground : Finset α) (x : α) (hx: x ∈ ground) (gcard: ground.card ≥ 2) : (ground.erase x).Nonempty :=
  by
    rw [Finset.erase_eq]
    apply Finset.nonempty_of_ne_empty
    by_contra h_empty
    by_cases hA : ground = ∅
    rw [hA] at gcard
    contradiction
    -- ground.card = 1のケース
    have g_eq_x: ground = {x} := by
      ext y
      constructor
      intro _
      have hy' : y ∈ ground \ {x} := by
          rw [h_empty]
          simp_all only [Finset.sdiff_eq_empty_iff_subset,Finset.subset_singleton_iff, false_or,Finset.singleton_ne_empty,Finset.card_singleton, Nat.not_ofNat_le_one]
      rw [h_empty] at hy'
      contradiction
      -- y ∈ {x}のときに、groundに属することを示す
      intro hy
      have x_eq_y : x = y := by
        rw [Finset.mem_singleton] at hy
        rw [hy]
      rw [x_eq_y] at hx
      exact hx
    rw [g_eq_x] at gcard
    rw [Finset.card_singleton] at gcard
    contradiction

-- Contraction操作の定義
def contraction (F : SetFamily α) (x : α) (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2): SetFamily α :=
  { ground := F.ground.erase x,

    sets := λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x,

    inc_ground := by
        intros s hs
        rcases hs with ⟨H, hH_sets, _, hs_eq⟩
        rw [hs_eq]
        --#check hH_sets -- F.sets H
        --#check hs_eq --s = H.erase x
        --goal H.erase x ⊆ F.ground.erase x
        intro y hy -- hy: y ∈ H.erase x
        rw [Finset.mem_erase] at hy
        rw [Finset.mem_erase]
        -- goal y ≠ x ∧ y ∈ F.ground
        constructor
        exact hy.1 -- x ¥neq y
        apply F.inc_ground H -- H ⊆ F.ground
        exact hH_sets -- F.sets H
        exact hy.2 --y ∈ H
        --なぜexactが3つもあるのか。

    nonempty_ground := ground_nonempty_after_deletion F.ground x hx gcard
  }

theorem Finset.erase_inj_of_mem {s t : Finset α} {x : α} (hx : x ∈ s) (ht : x ∈ t) :
  Finset.erase s x = Finset.erase t x ↔ s = t :=
by
  constructor
  -- まず、Finset.erase s x = Finset.erase t x から s = t を導きます。
  · intro h
    apply Finset.ext
    intro a
    by_cases ha : a = x
    -- a が x に等しい場合
    · rw [ha]
      simp_all

    -- a が x に等しくない場合
    simp only [ha, eq_self_iff_true] at h
    · constructor
      intro h1 -- a ∈ s
      have hh: a ∈ s.erase x := Finset.mem_erase_of_ne_of_mem ha h1
      rw [h] at hh
      exact Finset.mem_of_mem_erase hh
      intro h2 -- a ∈ t
      have hh: a ∈ t.erase x := Finset.mem_erase_of_ne_of_mem ha h2
      rw [←h] at hh
      exact Finset.mem_of_mem_erase hh

  -- 次に、s = t から Finset.erase s x = Finset.erase t x を導きます。
  · intro h
    rw [h]

lemma sum_eq (F : SetFamily α) (v : α) [DecidablePred F.sets] :
  (Finset.filter (λ s => F.sets s ∧ v ∈ s) (Finset.powerset F.ground)).sum (λ s => Finset.card s - 1) =
  (Finset.filter (λ s => ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v) (Finset.powerset (F.ground.erase v))).sum Finset.card :=
by
  -- 1. 両辺の和を比較するために、bijectionを構築します
  apply Finset.sum_bij (λ s _ => s.erase v)

  -- 2. bijectionの条件を証明します
  · intro s hs
    simp only [Finset.mem_filter] at hs ⊢
    constructor
    simp [hs.1,hs.2.2]
    intro y hy
    rw [Finset.mem_erase] at hy
    rw [Finset.mem_erase]
    constructor
    exact hy.1
    have sing: s ⊆ F.ground := F.inc_ground s hs.2.1
    exact sing hy.2
    --∃ H, F.sets H ∧ v ∈ H ∧ s.erase v = H.erase v
    use s
    exact ⟨hs.2.1, hs.2.2, rfl⟩

  -- 3. bijectionが単射であることを証明します

  · intro s hs t ht h
    simp only [Finset.mem_filter] at hs ht
    --theorem Finset.erase_inj {α : Type u_1}  [DecidableEq α]  {x : α}  {y : α}  (s : Finset α)  (hx : x ∈ s) :
    --Finset.erase s x = Finset.erase s y ↔ x = y

    apply (Finset.erase_inj_of_mem hs.2.2 ht.2.2).mp
    exact h

  -- 4. bijectionが全射であることを証明します
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_powerset] at hd
    simp only [Finset.mem_filter, Finset.mem_powerset]
    obtain ⟨hd₁, hd₂⟩ := hd
    obtain ⟨hd3, hd4, heq⟩ := hd₂
    have dd: v ∉ d := by
      intro hv
      -- 仮定 `h : d ⊆ F.erase v` を利用
      have h' : v ∈ F.ground.erase v := by
        simp [hd₁ hv]
      -- `v ∈ F.erase v` は矛盾
      have hfalse : v ∉ F.ground.erase v := by
        rw [Finset.mem_erase]
        simp
      contradiction

    use d ∪ {v}
    constructor

    exact union_erase_singleton d v dd
    ·constructor
     --goal d ∪ {v} ⊆ F.ground
     intro x hx
     simp only [Finset.mem_union, Finset.mem_singleton] at hx

     --同じ内容を2回証明してしまった。hd3vと同じ。
     /-have hd6: hd3 = (d ∪ {v}):= by
       rw [heq.2]
       rw [hd3.erase_eq]
       rw [erase_union_singleton hd3 heq.2 heq.1]
       rw [←Finset.erase_eq (d ∪ {v}) v]
       rw [union_erase_singleton d v dd]
     -/

     cases hx with
     | inl hx1 =>
       have hx_in_erase : x ∈ F.ground.erase v := Finset.mem_of_subset hd₁ hx1
       --theorem Finset.mem_of_subset {α : Type u_1}  {s₁ : Finset α}  {s₂ : Finset α}  {a : α} :
       --s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂
       exact Finset.mem_of_mem_erase hx_in_erase

     | inr hx2 =>
       --x = v
       simp [hx2, heq.2.symm]
       --goal v ∈ F.ground
       --hd4: F.sets hd3
       --heq.1: v ∈ hd3
       --subst v
       have hd3ground: hd3 ⊆ F.ground := F.inc_ground hd3 hd4
       exact hd3ground heq.1

    --h.w.right goal F.sets (d ∪ {v}) ∧ v ∈ d ∪ {v}
     constructor
      --goal F.sets (d ∪ {v})
     have hd3v: hd3 = d ∪ {v} := by
       rw [heq.2]
       rw [hd3.erase_eq]
       rw [erase_union_singleton hd3 heq.2 heq.1]
       simp

     have fsdv: F.sets (d ∪ {v}) := by
        exact hd3v ▸ hd4
     exact fsdv

     --goal v ∈ d ∪ {v}
     apply Finset.mem_union_right
     exact Finset.mem_singleton_self v

  -- 5. bijectionがwell-definedであることを証明します
  · intro s hs
    simp only [Finset.mem_filter] at hs
    rw [Finset.card_erase_of_mem hs.2.2]

lemma sum_of_size_eq_degree_plus_contraction_sum (F : SetFamily α) (v : α)
 (hg : F.ground.card ≥ 2) [DecidablePred F.sets] :
 (Finset.filter (λ s => F.sets s ∧ v ∈ s) (Finset.powerset F.ground)).sum Finset.card =
 degree F v + (Finset.filter (λ s => ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v) (Finset.powerset (F.ground.erase v))).sum Finset.card := by
  -- 1. degree の定義を展開
  rw [degree]

  -- 2. 左辺の和を二つの部分に分割
  have sum_split : (Finset.filter (λ s => F.sets s ∧ v ∈ s) (Finset.powerset F.ground)).sum Finset.card =
                   (Finset.filter (λ s => F.sets s ∧ v ∈ s) (Finset.powerset F.ground)).sum (λ s => 1 + (Finset.card s - 1)) := by
    apply Finset.sum_congr rfl
    intro s _
    dsimp
    rw [add_comm]
    rw [tsub_add_cancel_of_le]
    rename_i inst inst_1 _ inst_3 a
    simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, Finset.one_le_card]
    obtain ⟨_, right⟩ := a
    obtain ⟨_, right⟩ := right
    exact ⟨v, right⟩

  rw [sum_split]

  -- 3. 和の分配則を適用
  rw [Finset.sum_add_distrib]

  -- この補題は使わなかった。
  have _ : ∀ (s: Finset α), v ∈ s → 1 + (s.card - 1) = s.card :=
    fun s hvs => by
      have s1: 1 <= s.card := by
        apply Nat.one_le_of_lt
        apply Finset.card_pos.mpr
        exact ⟨v, hvs⟩
      rw [add_comm]
      rw [Nat.sub_add_cancel s1]

  -- 4. 左辺の最初の和が degree F v に等しいことを示す
  -- つまり、F.sets sになる回数だけ1が足されるので、degree F v に等しい
  have degree_eq : (Finset.filter (λ s => F.sets s ∧ v ∈ s) (Finset.powerset F.ground)).sum (λ _ => 1) = degree F v := by
    rw [Finset.sum_const]
    rw [degree]
    rw [all_subsets]
    simp_all

    --使いそうで使わなかったものたち。コメント消して良い。
    --simp only [Finset.card_eq_sum_ones]
    --simp only [sum_split]
    --rw [Finset.card_filter]
    --simp only [Finset.sum_ite, Finset.filter_true_of_mem]
    --convert sum_split
    --apply Finset.sum_congr rfl
    --rw [h s (Finset.mem_filter.mp hs).2.2]
  rw [degree_eq]

  -- 5. 残りの和の等価性を示す
  rw [sum_eq]
  rfl
