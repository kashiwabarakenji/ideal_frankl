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

namespace Mathematics

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

--vを含むhyperedgeの大きさの和は、vを含むhyperedgeをH-vを動かして作った集合族の大きさの和に等しい。
--次の定理で使う補題。
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

--vのを含むhyperedgeの大きさの和は、vの次数とvを含むhyperedgeからvを削除した大きさの和に等しい。
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

lemma erase_eq_iff_of_mem {s₁:Finset α}{s₂:Finset α}(hx1: x ∈ s₁)(hx2: x ∈ s₂): s₁.erase x = s₂.erase x → s₁ = s₂:= by
  intro h
  apply Finset.ext
  intro y
  by_cases hy : y = x
  · rw [hy]
    exact ⟨λ _ => hx2, λ _ => hx1⟩
  · have h1 : y ∈ s₁ ↔ y ∈ s₁.erase x := by
      constructor
      · intro hy1
        exact Finset.mem_erase.mpr ⟨hy, hy1⟩
      · intro hy1
        exact Finset.mem_of_mem_erase hy1
    have h2 : y ∈ s₂ ↔ y ∈ s₂.erase x := by
      constructor
      · intro hy2
        exact Finset.mem_erase.mpr ⟨hy, hy2⟩
      · intro hy2
        exact Finset.mem_of_mem_erase hy2
    --h1 : y ∈ s₁ ↔ y ∈ s₁.erase x
    rw [h1, h2, h]

lemma sumbij (F : SetFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) :
  let domain00 : Finset (Finset α):= (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)
  let range00 : Finset (Finset α) := (Finset.powerset (F.ground.erase x)).filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x)
  --domain0.card = range0.card := 証明したいことはこれではない。サイズの合計が等しいこと。
  domain00.sum Finset.card = range00.sum Finset.card + range00.card:=
  by
   let domain0 :Finset (Finset α):= (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)
   --have domain0have: domain0 = (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s):= by rfl
   let range0 :Finset (Finset α):= (Finset.powerset (F.ground.erase x)).filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x)
   --have range0have: range0 = (Finset.powerset (F.ground.erase x)).filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x):= by rfl
   -- 関数 f の定義
   let f := λ (s : Finset α) => Finset.card s
    -- 関数 g の定義
   let g := λ (s : Finset α) => (Finset.card s) + 1


   let ap := @Finset.sum_bij _ _ _ _ domain0 range0 f g
    (λ (s:Finset α) (_: s ∈ domain0) => s.erase x) --これは右側の集合から
   -- 写像の値が終域に含まれることの証明 うまくいっているのか。
    (by
     have index2: ∀ s ∈ domain0, s.erase x ∈ range0 :=
      by
        intros s hs
        dsimp [domain0] at hs
        dsimp [range0]
        simp only [Finset.mem_filter, Finset.mem_powerset] at hs
        --hs : s ⊆ F.ground ∧ F.sets s ∧ x ∈ s
        --goal s.erase x ∈ Finset.filter (fun s ↦ ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset
        rw [Finset.mem_filter]
        --goal s.erase x ∈ (F.ground.erase x).powerset ∧ ∃ H, F.sets H ∧ x ∈ H ∧ s.erase x = H.erase x
        constructor
        --s.erase x ∈ (F.ground.erase x).powerset
        rw [Finset.mem_powerset]
        -- goal s.erase x ⊆ F.ground.erase x
        apply Finset.erase_subset_erase
        exact hs.1

        -- goal ∃ H, F.sets H ∧ x ∈ H ∧ s.erase x = H.erase x
        use s
        exact ⟨hs.2.1, hs.2.2, rfl⟩
     exact index2
    )
    -- 写像が単射であることの証明
    (by
     have index3:  ∀ (a₁ : Finset α) (ha₁ : a₁ ∈ domain0) (a₂ : Finset α) (ha₂ : a₂ ∈ domain0),
     (fun s hs ↦ s.erase x) a₁ ha₁ = (fun s hs ↦ s.erase x) a₂ ha₂ → a₁ = a₂ :=
       by
         intros s₁ hs₁ s₂ hs₂ h
         dsimp [domain0] at hs₁ hs₂
         simp only [Finset.mem_filter, Finset.mem_powerset] at hs₁ hs₂
         --hs₁ : s₁ ⊆ F.ground ∧ F.sets s₁ ∧ x ∈ s₁
         --hs₂ : s₂ ⊆ F.ground ∧ F.sets s₂ ∧ x ∈ s₂
         --h: s₁.erase x = s₂.erase x
         let h1 := hs₁.2.2
         let h2 := hs₂.2.2
         exact erase_eq_iff_of_mem h1 h2 h
     -- goal  ∀ (a₁ : Finset α) (ha₁ : a₁ ∈ domain0) (a₂ : Finset α) (ha₂ : a₂ ∈ domain0),
     -- (fun s hs ↦ s.erase x) a₁ ha₁ = (fun s hs ↦ s.erase x) a₂ ha₂ → a₁ = a₂
     exact index3 --微妙な引数の順番の違いでエラーが出ていた。
    )
    -- 写像が全射であることの証明
    (by

     have index4: ∀ s ∈ range0, ∃H ∈ domain0, s = H.erase x :=
      by
        intros s hs
        simp only [Finset.mem_filter, Finset.mem_powerset] at hs
        dsimp [range0] at hs
        rw [Finset.mem_filter] at hs
        obtain ⟨H, hH1, hH2, hH3⟩ := hs.2
        --以下をいれるかいれないかで、使ってないのにエラーが出る。
        --have ss5: s ∪ {x} = H := by
        --  rw [hH3]
        --  exact (Mathematics.erase_insert H x hH2)
        use s ∪ {x}
        constructor
        -- goal s ∪ {x} ∈ range0
        dsimp [range0]
        rw [Finset.mem_filter]
        simp_all
        --H.erase x ∪ {x} ⊆ F.ground ∧ F.sets (H.erase x ∪ {x})
        constructor
        --hs.1: s ⊆ F.ground.erase x
        --x in F.ground
        -- から s ⊆ F.ground.erase xがいえる。
        --have s1: s ⊆ F.ground.erase x := by
        --  rename_i inst inst_1 inst_2 inst_3
        --  simp_all only

        have s2: s ∪ {x} ⊆ (F.ground.erase x)∪{x} := by
          rename_i inst inst_1 _ inst_3
          simp_all only [true_and]
          --obtain ⟨w, h⟩ := hs
          --obtain ⟨left, right⟩ := h
          --obtain ⟨left_1, right⟩ := right
          subst hH3
          -- x ∈ w ∧ s = w.erase x
          gcongr
          exact hs.1

        have s3: (F.ground.erase x)∪{x} = F.ground := by
          apply Mathematics.erase_insert F.ground x hx

        rw [s3] at s2
        -- hH1; F.sets H
        -- hH3: s = H.erase x
        have s5: s ∪ {x} = H := by
          rw [hH3]
          -- goal H.erase x ∪ {x} = H
          exact (Mathematics.erase_insert H x hH2)
        have he: H.erase x ∪ {x} = H:= by
          exact (Mathematics.erase_insert H x hH2)

        rw [he]
        rw [←s5]
        exact s2 --s ∪ {x} ⊆ F.ground
        --goal F.sets H
        rw [←hH3]
        --s5と同じだがすこーぷが違う。
        have HS: H = s ∪ {x} := by
          rw [hH3]
          --goal H = H.erase x ∪ {x}
          --#check Mathematics.erase_insert H x hH2
          exact (Mathematics.erase_insert H x hH2).symm
        rw [←HS]
        exact hH1
        --goal  s = (s ∪ {x}).erase x
        have s4: x ∉ s := by
          rename_i inst inst_1 _ inst_3
          subst hH3
          simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]
        exact (Mathematics.union_erase_singleton s x s4).symm
    --微妙にゴールと違ったので、書き換え。
     have index4':  ∀ b ∈ range0, ∃ a, ∃ (ha : a ∈ domain0), (fun s hs ↦ s.erase x) a ha = b :=
        by
          dsimp [range0,domain0]
          dsimp [range0,domain0] at index4
          simp
          simp at index4
          intro b hb c hc d hd
          let index4o := (index4 b hb c hc d hd)
          obtain ⟨H, hH1, hH2, hH3⟩ := index4o
          tauto
     exact index4'
    )

    (by
      --goal  ∀ (a : Finset α) (ha : a ∈ domain0), f a = g ((fun s hs ↦ s.erase x) a ha)
      --definition (h : ∀ (a : ι) (ha : a ∈ s), f a = g (i a ha))
      have index5 : ∀ (a : Finset α) (_ : a ∈ domain0),
        Finset.card a = Finset.card (a.erase x) + 1 :=
      by
        intros a ha
        dsimp [domain0] at ha
        simp only [Finset.mem_filter, Finset.mem_powerset] at ha

        -- `ha` より `x ∈ a` が成り立つことはすでに分かっている
        have hx : x ∈ a := by
          --simp at ha
          exact ha.2.2
        -- `Finset.card_erase_of_mem` を使ってカードの関係を証明
        rw [Finset.card_erase_of_mem hx]
        -- `Finset.card a = (Finset.card (a.erase x) + 1)` が得られる

        simp_all

        have c0: Finset.card a >= 1 := by
          apply Nat.one_le_of_lt
          apply Finset.card_pos.mpr
          exact ⟨x, hx⟩
        rename_i inst inst_1 _ inst_3 hx_1
        simp_all only [ge_iff_le, Finset.one_le_card, Nat.sub_add_cancel]

      have index5': ∀ (a : Finset α) (ha : a ∈ domain0), f a = g ((fun s _ ↦ s.erase x) a ha) :=
      by
        dsimp [f, g]
        dsimp [domain0]
        dsimp [domain0] at index5
        simp
        simp at index5
        intro a ha b hb
        --let index5o := (index5 a ha b hb)
        simp [range0, ha, index5, hb]

        have hx : x ∈ a := by
          --simp at ha
          exact hb
        have c0: Finset.card a >= 1 := by
          apply Nat.one_le_of_lt
          apply Finset.card_pos.mpr
          exact ⟨x, hx⟩
        rename_i inst inst_1 _ inst_3 hx_1
        simp_all only [ge_iff_le, Finset.one_le_card, Nat.sub_add_cancel]

      exact index5'
    )
   -- sum の分配と簡単な変形
   dsimp [domain0, range0]
   simp_all
   rw [←ap]
   dsimp [domain0, range0,range0] at ap
   --have domain_eq3: (∑ x ∈ domain0, f x) = (∑ (x ∈ Finset.filter (fun s ↦ F.sets s ∧ x ∈ s) F.ground.powerset), (f x)) := by rfl
   --have domain_eq2: domain0 = Finset.filter (fun s ↦ F.sets s ∧ x ∈ s) F.ground.powerset := by
   --  rw [←domain_eq]
   -- apの変換して標準化
   have domain_eq: domain0 = (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s) :=
      by rfl
   have range_eq: range0 = (Finset.powerset (F.ground.erase x)).filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) :=
      by rfl
   rw [←domain_eq,←range_eq] at ap
   have ghave: g = λ s => (Finset.card s) + 1 := by rfl
   rw [ghave] at ap
   rw [Finset.sum_add_distrib,Finset.sum_const] at ap
   have domain_eq4: ∑ x ∈ domain0, f x = domain0.sum Finset.card := by rfl
   rw [domain_eq4] at ap
   have range_eq3: ∑ x ∈ range0, x.card = range0.sum Finset.card := by rfl
   rw [range_eq3] at ap
   simp at ap
   rw [ap]

/-
lemma contraction_total_size (F : SetFamily α) [DecidablePred F.sets] (x : α)
  (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2) :
  total_size_of_hyperedges (Mathematics.contraction F x hx gcard) =
    ((Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)).sum (λ s => Finset.card s - 1)
-/

end Mathematics
