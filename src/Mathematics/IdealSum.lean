--Ideal集合族が平均abundantにならないことの証明が目標。

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic
import Mathematics.BasicDefinitions
import Mathematics.BasicLemmas
import Mathematics.IdealDeletion
import LeanCopilot
set_option maxHeartbeats 1000000

namespace Mathematics

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

--いまのところ補題を後ろで使っているわけではなさそう。今度使うかもしれないので、残しておく。
omit [Nonempty α] in
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


-- domain00とrange00に全単射が存在することを示した。
-- 今は他の部分では使ってなくてそれぞれ示しているが、これを利用できるはず。
omit [Nonempty α] in
theorem bf_bijective (F : SetFamily α) (x : α) [DecidablePred F.sets](hxG: x ∈ F.ground) :
  let domain00 : Finset (Finset α) := (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)
  let range00 : Finset (Finset α) := (Finset.powerset (F.ground.erase x)).filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x)
  Function.Bijective (λ (s : { S // S ∈ domain00 }) =>
    ⟨s.val.erase x, by
      simp [range00]
      rename_i inst inst_1 _ inst_3
      simp_all only [domain00]
      obtain ⟨val, property⟩ := s
      simp_all only
      simp_all only [Finset.mem_filter, Finset.mem_powerset, domain00]
      obtain ⟨left, right⟩ := property
      obtain ⟨left_1, right⟩ := right
      apply And.intro
      · intro y hy
        simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
        obtain ⟨_, right_1⟩ := hy
        exact left right_1
      · apply Exists.intro
        · apply And.intro
          on_goal 2 => {
            apply And.intro
            on_goal 2 => {apply Eq.refl
            }
            · simp_all only
          }
          · simp_all only
    ⟩ : { S // S ∈ domain00 } → { S // S ∈ range00 }):=
  by
    let domain00 : Finset (Finset α) := (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)
    constructor
    --1. 関数が単射であることを証明
    -- goal Function.Injective fun s ↦ ⟨(↑s).erase x, ⋯⟩
    dsimp [Function.Injective]
    -- goal ∀ ⦃a₁ a₂ : { S // S ∈ Finset.filter (fun s ↦ F.sets s ∧ x ∈ s) F.ground.powerset }⦄,
    --⟨(↑a₁).erase x, ⋯⟩ = ⟨(↑a₂).erase x, ⋯⟩ → a₁ = a₂
    intro a₁ a₂ h
    -- h: ⟨(↑a₁).erase x, ⋯⟩ = ⟨(↑a₂).erase x, ⋯⟩の条件から
    have h_erase : (a₁.val).erase x = (a₂.val).erase x := by
     simpa using h
    let a1p := a₁.property
    rw [Finset.mem_filter] at a1p
    let a2p := a₂.property
    rw [Finset.mem_filter] at a2p


    obtain ⟨_, _, a₁_x⟩ := a1p
    obtain ⟨_, _, a₂_x⟩ := a2p
    have eq_goal: a₁.val = a₂.val := by
     exact (Mathematics.erase_inj_of_mem a₁_x a₂_x).mp h_erase
    exact Subtype.eq eq_goal

    -- 2. 関数が全射であることを証明
    -- goal Function.Surjective fun s ↦ ⟨(↑s).erase x, ⋯⟩
    dsimp [Function.Surjective]
    intro b
    -- goal ∃ a, ⟨(↑a).erase x, ⋯⟩ = b
    -- 単に値だけでなく、propertyも同時に満たす必要がある。valの値とpropertyを満たすことを同時に示す。
    -- goal ⟨(↑b).erase x, ⋯⟩ = b
    let bp:= b.property
    rw [Finset.mem_filter] at bp
    obtain ⟨b_g, b_sets, b_x⟩ := bp
    let original := b.val ∪ {x}
    --originalが、domain00に属することを示す。
    have bpro: original ∈ domain00 := by
      simp_all only [domain00]
      --rename_i inst inst_1 _ inst_3
      simp_all only [Finset.mem_powerset, Finset.mem_filter, Finset.mem_union, Finset.mem_erase, ne_eq,
        not_true_eq_false, and_true, Finset.mem_singleton, or_true, original]
      obtain ⟨val, property⟩ := b
      obtain ⟨b_left, right⟩ := b_x
      obtain ⟨right_1, right_2⟩ := right
      simp_all only
      subst right_2
      have x_in_b: x ∈ b_sets := by
        simp_all only [right_1]
      have b_eq: b_sets.erase x ∪ {x} = b_sets := by
        exact (Mathematics.erase_insert b_sets x x_in_b)
      rw [b_eq]
      constructor
      --goal b_sets ⊆ F.ground
      have b_sets_ground: b_sets ⊆ F.ground := by
        -- bg: b_sets.erase x ⊆ F.ground.erase x
        --からいうのがいいのか。
        apply subset_of_erase_subset x_in_b hxG b_g

      simp_all only
      exact b_left

    --goal: ∃ a, ⟨(↑a).erase x, ⋯⟩ = b
    use ⟨original, bpro⟩
    simp_all only [Finset.mem_powerset, original]
    simp_all only [and_self]
    obtain ⟨val, property⟩ := b
    obtain ⟨left, right⟩ := b_x
    obtain ⟨left_1, right⟩ := right
    simp_all only [Subtype.mk.injEq]
    simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, Finset.mem_singleton, or_true, and_true,
      original, domain00]
    subst right
    obtain ⟨_, _⟩ := bpro
    ext1 a
    simp_all only [Finset.mem_erase, ne_eq, Finset.mem_union, Finset.mem_singleton, and_congr_right_iff,
      not_false_eq_true, true_and, or_false, implies_true]

--これはsubtypeでない。subtypeだとうまくいかなかったので、subtypeを使わないことを選択した。
def domain00 (F : SetFamily α) (v : α) [DecidablePred F.sets] : Finset (Finset α) :=
  (Finset.powerset F.ground).filter (λ s => F.sets s ∧ v ∈ s)

def range00 (F : SetFamily α) (v : α) [DecidablePred F.sets] :  Finset (Finset α) :=
  (Finset.powerset (F.ground.erase v)).filter (λ s => ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v)

-- s.val.erase v が range00 に属することを示す補題 subtype版
omit [Nonempty α] in
lemma f_mem_range00_sub (F : SetFamily α) (v : α) [DecidablePred F.sets]
  (s : { S // S ∈ domain00 F v }) : (s.val.erase v) ∈ (range00 F v) :=
by
  simp [range00]
  simp_all only [domain00]
  obtain ⟨val, property⟩ := s
  simp [domain00] at property
  obtain ⟨left, right⟩ := property
  obtain ⟨left_1, right⟩ := right
  apply And.intro
  · intro y hy
    simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
    obtain ⟨_, right_1⟩ := hy
    exact left right_1
  · apply Exists.intro
    · apply And.intro
      on_goal 2 => {
        apply And.intro
        on_goal 2 => {apply Eq.refl
        }
        · simp_all only
      }
      · simp_all only

omit [Nonempty α] in
lemma f_mem_range00 (F : SetFamily α) (v : α) [DecidablePred F.sets]
  (s : Finset α) (hs : s ∈ domain00 F v) : s.erase v ∈ range00 F v := by
  simp [range00]
  simp_all only [domain00]
  simp [domain00] at hs
  obtain ⟨left, right⟩ := hs
  obtain ⟨left_1, right⟩ := right
  apply And.intro
  · intro y hy
    simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
    obtain ⟨_, right_1⟩ := hy
    exact left right_1
  · apply Exists.intro
    · apply And.intro
      on_goal 2 => {
        apply And.intro
        on_goal 2 => {apply Eq.refl}
        · simp_all only
      }
      · simp_all only

--subtypeバージョンなので、使ってない。
def f (F : SetFamily α) (v : α) [DecidablePred F.sets] (s : { S // S ∈ domain00 F v }) : { S // S ∈ range00 F v } := ⟨s.val.erase v, f_mem_range00_sub F v s⟩

--subtypeバージョン 結局sum_bijの時は、subtypeバージョンはうまくいかないということがわかったので、使わなかった。
def f_wrapped_sub (F : SetFamily α) (v : α) [DecidablePred F.sets]
  (s : { S // S ∈ domain00 F v }) : { T // T ∈ range00 F v } :=
  ⟨s.val.erase v, f_mem_range00_sub F v s⟩
--非subtypeバージョン
def f_wrapped (F : SetFamily α) (v : α) [DecidablePred F.sets]
  (s : Finset α) (_ : s ∈ domain00 F v) : Finset α :=
  s.erase v

--f_wrappedのなかに単射の証拠がはいってなくて、bf_bijectiveのなかなので、困る。
omit [Nonempty α] in
lemma injective_f_wrapped (F : SetFamily α) (v : α) [DecidablePred F.sets] (hvG: v ∈ F.ground)
  (a₁ : Finset α) (ha₁ : a₁ ∈ domain00 F v)
  (a₂ : Finset α) (ha₂ : a₂ ∈ domain00 F v)
  (h : f_wrapped F v a₁ ha₁ = f_wrapped F v a₂ ha₂) : a₁ = a₂ :=
by
  have bij_inj := (bf_bijective F v hvG).1
  rw [Function.Injective] at bij_inj
  --単射性を示したいが、bijectiveの条件から単射性を取り出すのが意外と難しい。

  --#check  a₁ f_wrappedを用いているため、これはsubtypeではない。obtainを2回行って、subtypeでない値を取り出している。
  have v_in_a1:v ∈ a₁ := by
    simp [domain00] at ha₁
    obtain ⟨_, right⟩ := ha₁
    obtain ⟨_, right⟩ := right
    exact right

  have v_in_a2:v ∈ a₂ := by
    simp [domain00] at ha₂
    obtain ⟨_, right⟩ := ha₂
    obtain ⟨_, right⟩ := right
    exact right

  apply (Mathematics.erase_inj_of_mem v_in_a1 v_in_a2).mp
  exact h

omit [Nonempty α] in
lemma surjective_f_wrapped (F : SetFamily α) (v : α) [DecidablePred F.sets] (hvG: v ∈ F.ground)
  (b : Finset α) (hb : b ∈ range00 F v) :
  ∃ a, ∃ ha : a ∈ domain00 F v, f_wrapped F v a ha = b :=
by
  have bij_sur := (bf_bijective F v hvG).2
  rw [Function.Surjective] at bij_sur
  --#check bij_sur

  -- `bij_sur` に基づいてサブタイプ `b` に対する結果を展開
  obtain ⟨a, ha⟩ := bij_sur ⟨b, hb⟩
  -- `a` と `ha` を `f_wrapped` に適用して全射性を証明
  use a.val
  use a.property
  --refine ⟨a.val, a.property, _⟩
  have : f_wrapped F v a.val a.property = b := by
    simp [f_wrapped]
    -- `congr_arg` を使用して等式を変換
    --rename_i inst inst_1 _ inst_3
    simp_all only [Subtype.exists, Finset.mem_filter, Finset.mem_powerset, Subtype.forall, Subtype.mk.injEq,
      exists_prop, and_imp, forall_exists_index]
  exact this

omit [Nonempty α] in
lemma card_equal (F : SetFamily α) (v : α) [DecidablePred F.sets](hvG: v ∈ F.ground) :
  (Finset.filter (λ s => F.sets s ∧ v ∈ s) (Finset.powerset F.ground)).card =
  (Finset.filter (λ s => ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v) (Finset.powerset (F.ground.erase v))).card :=
by
  --let domain00 : Finset (Finset α) := (Finset.powerset F.ground).filter (λ s => F.sets s ∧ v ∈ s)
  --let range00 : Finset (Finset α) := (Finset.powerset (F.ground.erase v)).filter (λ s => ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v)
  --let f_wrapped := λ (s : Finset α) (hs : s ∈ (domain00 F v)) => ⟨s.val.erase v, f_mem_range00 F v s⟩--(f F v ⟨s, hs⟩).val
  --have bij := bf_bijective F v hvG

  let bij_inj := injective_f_wrapped F v hvG
  let bij_sur := surjective_f_wrapped F v hvG

  --subtypeを用いる方法では結局うまくいかなさそう。
  --let Fincard_sub := @Finset.card_bij (Finset α) (Finset α) (domain00 F v) (range00 F v) (f_wrapped_sub F v)
  let Fincard := @Finset.card_bij (Finset α) (Finset α) ( domain00 F v) (range00 F v) (f_wrapped F v) (f_mem_range00 F v) bij_inj bij_sur
    --(∀ (s : Finset α), (s ∈ (domain00 F v))→(f_mem_range00 F v s))
    --(∀ (s : { S // S ∈ domain00 F v }), (f_mem_range00 F v s))
  exact Fincard

  --Finset.card_bij {α : Type u_1}  {β : Type u_2}  {s : Finset α} {t : Finset β}  (i : (a : α) → a ∈ s → β) (hi : ∀ (a : α) (ha : a ∈ s), i a ha ∈ t) (i_inj : ∀ (a₁ : α) (ha₁ : a₁ ∈ s) (a₂ : α) (ha₂ : a₂ ∈ s), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂) (i_surj : ∀ b ∈ t, ∃ (a : α) (ha : a ∈ s), i a ha = b) :
  --s.card = t.card

-- Contraction操作の定義
--IdealDeletion.leanにあるcontractionの定義を使うべき。
def contraction (F : SetFamily α) (x : α) (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2): SetFamily α :=
  { ground := F.ground.erase x,

    sets := λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x,

    inc_ground := by
        intros s hs
        rcases hs with ⟨H, hH_sets, _, hs_eq⟩
        rw [hs_eq]
        --goal H.erase x ⊆ F.ground.erase x
        intro y hy -- hy: y ∈ H.erase x
        rw [Finset.mem_erase] at hy
        rw [Finset.mem_erase]
        -- goal y ≠ x ∧ y ∈ F.groundv
        constructor
        exact hy.1 -- x ¥neq y
        apply F.inc_ground H -- H ⊆ F.ground
        exact hH_sets -- F.sets H
        exact hy.2 --y ∈ H
        --なぜexactが3つもあるのか。

    nonempty_ground := Mathematics.ground_nonempty_after_minor F.ground x hx gcard
  }


--vを含むhyperedgeの大きさの和は、vを含むhyperedgeをH-vを動かして作った集合族の大きさの和に等しい。
--次の定理で使う補題。
omit [Nonempty α] in
lemma sum_equal (F : SetFamily α) (v : α) [DecidablePred F.sets] :
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

    apply (Mathematics.erase_inj_of_mem hs.2.2 ht.2.2).mp
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
omit [Nonempty α] in
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
    rename_i _ _ _ a
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

  rw [degree_eq]

  -- 5. 残りの和の等価性を示す
  rw [sum_equal]
  rfl


omit [Nonempty α] in
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
         exact Mathematics.set_eq_of_erase_eq h1 h2 h
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

        have s2: s ∪ {x} ⊆ (F.ground.erase x)∪{x} := by
          --rename_i inst inst_1 _ inst_3
          simp_all only [true_and]
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
          --rename_i inst inst_1 _ inst_3
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
        --rename_i inst inst_1 _ inst_3 hx_1
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
        --rename_i inst inst_1 _ inst_3 hx_1
        simp_all only [ge_iff_le, Finset.one_le_card, Nat.sub_add_cancel]

      exact index5'
    )
   -- sum の分配と簡単な変形
   dsimp [domain0, range0]
   simp_all
   rw [←ap]
   dsimp [domain0, range0,range0] at ap
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

----------

def ff (s: Finset α): ℕ := Finset.card s - 1

omit [Nonempty α] in
lemma contraction_family_size (F : SetFamily α) [DecidablePred F.sets] (x : α)
  (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2) : total_size_of_hyperedges (Mathematics.contraction F x hx gcard) = (Finset.filter (fun s ↦ ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset).sum Finset.card :=
  by
    rw [total_size_of_hyperedges]
    dsimp [Mathematics.contraction]
    rw [Finset.filter_congr_decidable]

omit [Nonempty α] in
lemma contraction_total_size (F : SetFamily α) [DecidablePred F.sets] (x : α)
  (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2) :
  total_size_of_hyperedges (Mathematics.contraction F x hx gcard) =
    ((Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)).sum (λ s => Finset.card s - 1) :=
  by
    rw [total_size_of_hyperedges]
    let largeset:= Finset.filter (fun s ↦ F.sets s ∧ x ∈ s) F.ground.powerset
    --have largesethave: largeset = Finset.filter (fun s ↦ F.sets s ∧ x ∈ s) F.ground.powerset := by rfl
    let smallset:= Finset.filter (fun s ↦ ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset
    --have smallsethave: smallset = Finset.filter (fun s ↦ ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset := by rfl
    have sum_eq0 := sum_of_size_eq_degree_plus_contraction_sum F x gcard
    have sum_eq2 := sumbij F x hx
    simp_all

    have substitute1: (Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum (λ s => Finset.card s - 1) = largeset.sum (λ s => Finset.card s - 1) := by rfl
    have substitute2: (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum Finset.card = smallset.sum Finset.card := by rfl
    rw [←substitute1]
    have sum_eq3 : ∑ s ∈ largeset, (s.card - 1) = largeset.sum (λ s => s.card - 1) := by rfl
    rw [←sum_eq3]

    have f_eq : ∀ s ∈ largeset, ff s = Finset.card s - 1 := by
        intros s _
        simp only [ff]

    have sum_eq3: largeset.sum (λ s => s.card - 1) = largeset.sum ff := by rfl
    have sum_eq5: largeset.sum (ff) + largeset.card = largeset.sum (λ s => ff s + 1) := by
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_const]
      simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, Finset.one_le_card, and_imp, Pi.sub_apply,
        Pi.one_apply, smul_eq_mul, mul_one, smallset, largeset]

    let contset := (Finset.filter (contraction F x hx gcard).sets (contraction F x hx gcard).ground.powerset)
    have contsethave: contset = (Finset.filter (contraction F x hx gcard).sets (contraction F x hx gcard).ground.powerset) := by rfl
    rw [←contsethave]

    have substitute3: (Finset.filter (contraction F x hx gcard).sets (contraction F x hx gcard).ground.powerset).sum Finset.card = contset.sum Finset.card := by rfl
    rw [substitute3]
    have sum_eq4 : ∑ s ∈ largeset, (s.card - 1) = largeset.sum (λ s => s.card - 1) := by rfl
    rw [←sum_eq4]
    rw [sum_eq3]
    rw [substitute2] at sum_eq0
    rw [substitute2] at sum_eq0
    have substitute4: (Finset.filter (fun s ↦ ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset).card  = smallset.card := by rfl
    rw [substitute4] at sum_eq0
    --#check sum_eq0 --smallset.sum Finset.card + smallset.card = degree F x + smallset.sum Finset.card

    let sumbijlocal := sumbij F x hx
    -- let domain00 := Finset.filter (fun s ↦ F.sets s ∧ x ∈ s) F.ground.powerset;
    have sumbijihave :largeset.sum Finset.card = smallset.sum Finset.card + smallset.card := sumbij F x hx

    let contsizelocal := contraction_family_size F x hx gcard
    dsimp [total_size_of_hyperedges] at contsizelocal
    rw [substitute3] at contsizelocal
    rw [substitute2] at contsizelocal
    rw [contsizelocal]
    --goal  smallset.sum Finset.card = largeset.sum ff
    --sumbijhave: largeset.sum Finset.card = smallset.sum Finset.card + smallset.card
    --goalは、sumbijhaveを移項したもの。よって、あとは、largeset.sum Finset.card 　>=  smallset.cardがわかればよい。

    have positive: ∀ s ∈ largeset, s.card ≥ 1 := by
      intros s hs
      simp only [Finset.mem_filter] at hs
      rename_i inst _ _ _
      simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, Finset.one_le_card, smallset, largeset]
      obtain ⟨_, right⟩ := hs
      obtain ⟨_, right⟩ := right
      exact ⟨x, right⟩

    have largesum_lt_smallcard: largeset.sum Finset.card >= largeset.card := by
      have largesum_ge_1: ∀ s ∈ largeset, s.card >= 1 := by
        intros s hs
        simp only [Finset.mem_filter] at hs
        exact positive s hs
      calc
        largeset.sum Finset.card = largeset.sum (λ s=> s.card) := by simp
        _ >= largeset.sum (λ s => 1) := Finset.sum_le_sum largesum_ge_1
        _ = largeset.card * 1 := by
          --rename_i inst inst_1 _ inst_3 _
          simp_all only [Finset.mem_filter, Finset.mem_powerset, ge_iff_le, and_self, and_imp, implies_true,
            Finset.one_le_card, Finset.sum_const, smul_eq_mul, mul_one, smallset, sumbijlocal, largeset, contset]
        _ = largeset.card := by simp

    have largecard_eq_smallcard: largeset.card = smallset.card := by
        dsimp [largeset]
        dsimp [smallset]
        exact (card_equal F x hx)

    rw [largecard_eq_smallcard] at largesum_lt_smallcard
    rw [ge_iff_le] at largesum_lt_smallcard
    --sumbijhave: largeset.sum Finset.card = smallset.sum Finset.card + smallset.card
    --goal: smallset.sum Finset.card = largeset.sum ff = largeset.sum Finset.card - smallset.card

    have calc0 : (largeset.sum Finset.card) - smallset.card = smallset.sum Finset.card := by
      calc
        largeset.sum Finset.card -smallset.card
            = (smallset.sum Finset.card + smallset.card) - smallset.card := by rw [sumbijihave]
          _ = smallset.sum Finset.card  := by rw [Nat.add_sub_cancel]

    rw [←calc0]
    rw [←largecard_eq_smallcard]

    have sum_subst: largeset.sum (λ s => ff s + 1) = largeset.sum Finset.card := by
      dsimp [ff]
      apply Finset.sum_congr rfl
      intro s hs
      -- s.card - 1 + 1 = s.card を示す
      rw [Nat.sub_add_cancel (positive s hs)]

    rw [sum_subst] at sum_eq5
    -- sum_eq5: largeset.sum ff + largeset.card = largeset.sum Finset.card
    -- goal largeset.sum Finset.card - largeset.card = largeset.sum ff
    rw [←sum_eq5]
    --goal largeset.sum ff + largeset.card - largeset.card = largeset.sum ff
    rw [Nat.add_sub_cancel]



omit [Nonempty α] in
lemma filter_sum_eq (F : SetFamily α) (x : α) (hx : x ∈ F.ground) [DecidablePred F.sets] :
  (Finset.filter (λ s => F.sets s ∧ x ∉ s) F.ground.powerset).sum Finset.card =
  (Finset.filter (λ s => F.sets s ∧ x ∉ s) (F.ground.erase x).powerset).sum Finset.card :=
by

  -- `h1` を用いて、式を簡略化
  apply Finset.sum_congr
  apply Finset.ext
  intro s
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase]
  -- 明示的には以下の補題は使ってないが、裏で役に立っている。
  have lem: x ∉ s → ( s ⊆ F.ground ↔ s ⊆ F.ground.erase x) := by
    intro h
    constructor
    intro a
    intro y
    intro hy
    by_cases h1: y = x
    rw [h1] at hy
    subst h1
    contradiction
    simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
    exact a hy
    intro h2
    exact h2.trans (Finset.erase_subset _ _)

  simp_all only [and_congr_left_iff, not_false_eq_true, and_imp, implies_true]

  intro x_1 _

  simp_all only [Finset.mem_filter, Finset.mem_powerset]

----idealdeletionじゃなくて、deletionで等式を証明して、そこから(hx_hyperedge : F.sets (F.ground \ {x}))かどうかで分岐するのが良いかもしれない。
---F.sets (F.ground \ {x}))が成り立つかどうかでidealdeletionとdeletionの関係を書く。TODO:
theorem hyperedge_totalsize_deletion_contraction{α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2)
  [DecidablePred F.sets]  :
  total_size_of_hyperedges F.toSetFamily =
  total_size_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard)  +
  total_size_of_hyperedges (IdealDeletion.contraction F.toSetFamily x hx gcard) + degree F.toSetFamily x:=
by
    have sub1 :  total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∈ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } =
    (Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum Finset.card := by
      rfl

    have sub2: total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∉ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } =
    (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
      rfl

    have sub3: (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum Finset.card =
       total_size_of_hyperedges  (IdealDeletion.contraction F.toSetFamily x hx gcard) := by
      dsimp [total_size_of_hyperedges]
      dsimp [IdealDeletion.contraction]
      congr

    have sub4: (Finset.filter (λ s => F.sets s ∧ x  ∉ s) (Finset.powerset F.ground)).sum Finset.card = total_size_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard) := by
      dsimp [total_size_of_hyperedges]
      dsimp [IdealDeletion.deletion]
      rw [filter_sum_eq]
      congr
      exact hx

    calc
      total_size_of_hyperedges F.toSetFamily
          = total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∈ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } +
            total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∉ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } := by
              rw [←(sum_partition_by_v F.toSetFamily x)]
       _  = (Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum Finset.card +
            (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
              rw [sub1]
              rw [sub2]
       _  = degree F.toSetFamily x + (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum Finset.card +
            (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
              rw [sum_of_size_eq_degree_plus_contraction_sum F.toSetFamily x gcard]
       _  = degree F.toSetFamily x + total_size_of_hyperedges  (IdealDeletion.contraction F.toSetFamily x hx gcard)
               + (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
              rw [sub3]
       _  = degree F.toSetFamily x + total_size_of_hyperedges  (IdealDeletion.contraction F.toSetFamily x hx gcard) +
            total_size_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard) := by
              rw [sub4]
       _  = total_size_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard)  +
            total_size_of_hyperedges (IdealDeletion.contraction F.toSetFamily x hx gcard) + degree F.toSetFamily x := by
              ring

theorem hyperedge_totalsize_deletion_contraction_have {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2)
  [DecidablePred F.sets] (hx_hyperedge : F.sets (F.ground \ {x})) :
  total_size_of_hyperedges F.toSetFamily =
  total_size_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily  +
  total_size_of_hyperedges (IdealDeletion.contraction F.toSetFamily x hx gcard) + degree F.toSetFamily x:=

  by
    --#check sum_partition_by_v F.toSetFamily x
    have sub1 :  total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∈ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } =
    (Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum Finset.card := by
      rfl

    have sub2: total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∉ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } =
    (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
      rfl

    have sub3: (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum Finset.card =
       total_size_of_hyperedges  (IdealDeletion.contraction F.toSetFamily x hx gcard) := by
      dsimp [total_size_of_hyperedges]
      dsimp [IdealDeletion.contraction]
      congr

    have sub4: (Finset.filter (λ s => F.sets s ∧ x  ∉ s) (Finset.powerset F.ground)).sum Finset.card = total_size_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard) := by
      dsimp [total_size_of_hyperedges]
      dsimp [IdealDeletion.deletion]
      rw [filter_sum_eq]
      congr
      exact hx

    have sub5: (IdealDeletion.idealdeletion F x hx gcard).toSetFamily = (IdealDeletion.deletion F.toSetFamily x hx gcard) := by
      rw [IdealDeletion.idealdeletion]
      rw [IdealDeletion.deletion]
      simp_all
      ext x_1 : 2
      simp_all only [or_iff_left_iff_imp, Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]
      intro a
      subst a
      convert hx_hyperedge
      ext1 a
      simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
      apply Iff.intro
      · intro a_1
        simp_all only [not_false_eq_true, and_self]
      · intro a_1
        simp_all only [not_false_eq_true, and_self]
    calc
      total_size_of_hyperedges F.toSetFamily
          = total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∈ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } +
            total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ x ∉ s, inc_ground := λ s hs => F.inc_ground s (hs.1) } := by
              rw [←(sum_partition_by_v F.toSetFamily x)]
       _  = (Finset.filter (λ s => F.sets s ∧ x ∈ s) (Finset.powerset F.ground)).sum Finset.card +
            (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
              rw [sub1]
              rw [sub2]
       _  = degree F.toSetFamily x + (Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (Finset.powerset (F.ground.erase x))).sum Finset.card +
            (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
              rw [sum_of_size_eq_degree_plus_contraction_sum F.toSetFamily x gcard]
       _  = degree F.toSetFamily x + total_size_of_hyperedges  (IdealDeletion.contraction F.toSetFamily x hx gcard)
               + (Finset.filter (λ s => F.sets s ∧ x ∉ s) (Finset.powerset F.ground)).sum Finset.card := by
              rw [sub3]
       _  = degree F.toSetFamily x + total_size_of_hyperedges  (IdealDeletion.contraction F.toSetFamily x hx gcard) +
            total_size_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard) := by
              rw [sub4]
       _  = degree F.toSetFamily x + total_size_of_hyperedges  (IdealDeletion.contraction F.toSetFamily x hx gcard) +
            total_size_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily := by
              rw [←sub5]
       _  = total_size_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily +
            total_size_of_hyperedges (IdealDeletion.contraction F.toSetFamily x hx gcard) +(degree F.toSetFamily x):= by
              ring

omit [Fintype α] [Nonempty α] in
theorem filter_powerset_sum {A : Finset α} (h : x ∈ A):
  (A.powerset.filter (fun s => s = A.erase x)).sum Finset.card = A.card - 1 :=
  by
    -- フィルタされた部分集合は A.erase x のみを含む
    have h₁ : (A.powerset.filter (fun s => s = A.erase x)) = {A.erase x} := by
      ext s
      simp [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      intro a
      subst a
      intro y hy
      simp_all only [Finset.mem_erase, ne_eq]

    -- sum 関数の適用
    rw [h₁, Finset.sum_singleton]
       -- A.erase x の要素数は A.card - 1

    exact Finset.card_erase_of_mem h


lemma disjoint_sum_card_eq {α : Type*} [DecidableEq α] {A B : Finset (Finset α)} (h : A ∩ B = ∅) :
  (A ∪ B).sum Finset.card = A.sum Finset.card + B.sum Finset.card :=
by
  -- `A ∩ B = ∅` という仮定から、A と B が互いに素であることを示す
  have h_disjoint : Disjoint A B := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact h

  -- `sum_union` を使って A ∪ B の和が A と B の和に分かれることを証明
  symm
  rw [Finset.sum_union h_disjoint]

lemma ideal_and_deletion {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2) (hx_hyperedge_not : ¬ F.sets (F.ground \ {x})) :
  total_size_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily = total_size_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard) + (F.ground.card - 1):=
  by

    have sub4: (Finset.filter (λ s => F.sets s ∧ x  ∉ s) (Finset.powerset F.ground)).sum Finset.card = total_size_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard) := by
      dsimp [total_size_of_hyperedges]
      dsimp [IdealDeletion.deletion]
      rw [filter_sum_eq]
      congr
      exact hx

    rw [←sub4]
    rw [total_size_of_hyperedges]
    simp_all
    rw [IdealDeletion.idealdeletion]
    rw [total_size_of_hyperedges]
    rw [IdealDeletion.deletion]

    have disj: Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) F.ground.powerset ∩ Finset.filter (fun s ↦ s = F.ground.erase x) F.ground.powerset = ∅ := by
      apply Finset.eq_empty_of_forall_not_mem
      intro a
      simp_all only [Finset.mem_inter, Finset.mem_filter, Finset.mem_powerset]
      intro h
      obtain ⟨h1, h2⟩ := h
      simp_all only [and_self, and_true, not_false_eq_true, and_imp, implies_true, not_true_eq_false]
      let state1 := h1.2.1
      rw [←(Finset.sdiff_singleton_eq_erase x (F.ground))] at state1
      contradiction

    rw [←Finset.disjoint_iff_inter_eq_empty] at disj --Disjointに。

    have sub6:  (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) F.ground.powerset ∪
        Finset.filter (fun s ↦ s = F.ground.erase x) F.ground.powerset).card =
    (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) F.ground.powerset).card +
      (Finset.filter (fun s ↦ s = F.ground.erase x) F.ground.powerset).card := by
        apply (Finset.card_union_of_disjoint disj) --効果なし？

    have sub7: (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) F.ground.powerset ∪
        Finset.filter (fun s ↦ s = F.ground.erase x) F.ground.powerset) =  (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) F.ground.powerset) := by
        apply Finset.ext
        intro a
        simp_all only [Finset.mem_union, Finset.mem_filter, Finset.mem_powerset]
        apply Iff.intro
        intro h
        simp_all only [Finset.card_union_of_disjoint]
        cases h with
        | inl h_1 => simp_all only [not_false_eq_true, and_self, true_or]
        |
          inr h_2 =>
          simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true, or_true]
          obtain ⟨left, right⟩ := h_2
          subst right
          simp_all only
        intro a_1
        simp_all only [Finset.card_union_of_disjoint, true_and]

    have sub8: ((Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) F.ground.powerset ∪ Finset.filter (fun s ↦ s = F.ground.erase x) F.ground.powerset)).sum Finset.card =
     (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) F.ground.powerset).sum Finset.card := by
      rw [sub7]

    have sub9:Finset.filter (λ s=> F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) F.ground.powerset = Finset.filter (λ s=> F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) (F.ground.erase x).powerset
      := by
        apply Finset.ext
        intro ss
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase]
        apply Iff.intro
        intro a
        obtain ⟨left, right⟩ := a
        constructor
        cases right with
        | inl h =>
          --left : ss ⊆ F.groundとright : x ∉ ssから、ss ⊆ F.ground.erase xを示す。
          intro y
          intro hy
          rw [Finset.erase_eq]
          rw [Finset.mem_sdiff]
          constructor
          --goal y ∈ F.ground
          exact left hy
          --goal y ≠ x
          intro hh
          have xy: x = y := by
            rw [Finset.mem_singleton] at hh
            exact hh.symm
          rw [xy]  at h
          let hright:= h.2
          contradiction
        | inr h =>
          subst h
          rfl
        --goal F.sets ss ∧ x ∉ ss ∨ ss = F.ground.erase x
        cases right with
        | inl h =>
          exact Or.inl h
        | inr h =>
          exact Or.inr h
        --多分逆方向
        intro aa
        obtain ⟨left0, right0⟩ := aa
        constructor
        cases right0 with
        | inl h =>
          --left0 : ss ⊆ F.ground.erase xとright0 : x ∉ ssから、ss ⊆ F.groundを示す。
          intro y
          intro hy
          --y ∈ F.ground
          let hy1 := left0 hy
          rw [Finset.erase_eq] at hy1
          rw [Finset.mem_sdiff] at hy1
          exact hy1.1
        | inr h =>
          subst h
          intro y hy
          rw [Finset.mem_erase] at hy
          exact hy.2
        --goal F.sets ss ∧ x ∉ ss ∨ ss = F.ground.erase x
        exact right0

    have sub11: (Finset.filter (fun s => s = F.ground.erase x) F.ground.powerset) = {F.ground.erase x} := by
      apply Finset.ext
      intro s
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      apply Iff.intro
      intro a

      obtain ⟨_, right⟩ := a
      exact right

      intro a
      constructor
      have lem: F.ground.erase x ⊆ F.ground := by
        exact Finset.erase_subset x F.ground
      rw [←a] at lem
      exact lem
      exact a

    have sub10: (Finset.filter (fun s => s = F.ground.erase x) F.ground.powerset).sum Finset.card = (F.ground.card - 1) := by
      rw [sub11]
      simp_all only [Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, ne_eq,
        not_true_eq_false, and_true, not_false_eq_true, not_and, implies_true, Finset.card_union_of_disjoint,
        Finset.card_singleton, Finset.sum_singleton, Finset.card_erase_of_mem]

    set h_lhs := (Finset.filter (λ s=> F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) F.ground.powerset).sum Finset.card with h_lhs_def
    set h_rhs := (Finset.filter (λ s=> F.sets s ∧ x ∉ s) F.ground.powerset).sum Finset.card + (F.ground.card - 1) with h_rhs_def
    set h_rhs0 := (Finset.filter (λ s=> F.sets s ∧ x ∉ s) F.ground.powerset).sum Finset.card with h_rhs0_def
    set h_lhs1 := Finset.filter (λ s=> F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) F.ground.powerset with h_lhs1_def
    set h_rhs1 := Finset.filter (λ s=> F.sets s ∧ x ∉ s) F.ground.powerset with h_rhs1_def

    have sub9': h_lhs1 = Finset.filter (λ s=> F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) (F.ground.erase x).powerset :=
      by
        rw [←sub9]

    have goal1: h_lhs = h_rhs := by --h_rhs_defだとエラーになる。
      dsimp [h_lhs, h_rhs]
      dsimp [h_lhs] at sub8
      rw [←sub8]
      rw [←sub10]

      rw [Finset.disjoint_iff_inter_eq_empty] at disj
      rw [←(disjoint_sum_card_eq disj)]

    simp only [h_lhs_def, h_rhs_def] at goal1
    simp only [h_lhs1_def, h_rhs1_def,h_rhs0] at goal1

    set h_lhs_e := (Finset.filter (λ s=> F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) (F.ground.erase x).powerset).sum Finset.card with h_lhs_def
    set h_rhs_e := (Finset.filter (λ s=> F.sets s ∧ x ∉ s) (F.ground.erase x).powerset).sum Finset.card + (F.ground.card - 1) with h_rhs_def
    set h_rhs0_e := (Finset.filter (λ s=> F.sets s ∧ x ∉ s) (F.ground.erase x).powerset).sum Finset.card  with h_rhs0_e_def

    have goal_e: h_lhs_e = h_rhs_e := by
      dsimp [h_lhs_e, h_rhs_e]
      rw [←sub9]
      rw [goal1]
      rw [←h_rhs0_def]
      rw [←h_rhs_def]
      have sub12: h_rhs0 + (F.ground.card - 1) = h_rhs := by
        dsimp [h_rhs0]
      rw [sub12]
      dsimp [h_rhs, h_rhs_e]
      rw [←h_rhs0_def]
      rw [←h_rhs0_e_def]

      have goale1: (Finset.filter (fun s => F.sets s ∧ x ∉ s) F.ground.powerset) =(Finset.filter (fun s => F.sets s ∧ x ∉ s) (F.ground.erase x).powerset):=
        by
          apply Finset.ext
          intro s
          simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase]
          apply Iff.intro
          intro a
          obtain ⟨left, right⟩ := a
          constructor
          intro y
          intro hy
          simp_all only [Finset.sum_singleton, Finset.card_erase_of_mem, Finset.disjoint_singleton_right,
            Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
            not_false_eq_true, not_and, implies_true, Finset.card_union_of_disjoint, Finset.card_singleton, h_rhs0,
            h_rhs, h_lhs1, h_lhs, h_rhs1, h_lhs_e, h_rhs_e, h_rhs0_e]
          obtain ⟨_, right⟩ := right
          apply And.intro
          · apply Aesop.BuiltinRules.not_intro
            intro a
            subst a
            simp_all only
          · exact left hy
          simp_all only [Finset.sum_singleton, Finset.card_erase_of_mem, Finset.disjoint_singleton_right,
            Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
            not_false_eq_true, not_and, implies_true, Finset.card_union_of_disjoint, Finset.card_singleton, and_self,
            h_rhs0, h_rhs, h_lhs1, h_lhs, h_rhs1, h_lhs_e, h_rhs_e, h_rhs0_e]
          --goal s ⊆ F.ground.erase x ∧ F.sets s ∧ x ∉ s → s ⊆ F.ground ∧ F.sets s ∧ x ∉ s

          intro a
          obtain ⟨left_1, right⟩ := a
          constructor
          · intro y
            intro hy
            simp_all only [Finset.mem_erase, Finset.mem_sdiff]
            have lem: F.ground.erase x ⊆ F.ground := by
              simp_all only [Finset.sum_singleton, Finset.card_erase_of_mem, Finset.disjoint_singleton_right,
                Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
                not_false_eq_true, not_and, Finset.card_singleton, h_rhs, h_rhs0, h_lhs1, h_lhs_e]
              --obtain ⟨left, right⟩ := right
              intro z hz
              simp_all only [Finset.mem_erase, ne_eq]
            have lem2: s  ⊆ F.ground := by
              exact subset_trans left_1 lem
            exact lem2 hy
          · exact right

      have goal_e0: h_rhs0 = h_rhs0_e := by
        dsimp [h_rhs0, h_rhs0_e]
        rw [←goale1]
      rw [←goal_e0]
    simp_all only [Finset.sum_singleton, Finset.card_erase_of_mem, Finset.disjoint_singleton_right, Finset.mem_filter,
      Finset.mem_powerset, Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true, not_and,
      implies_true, Finset.card_union_of_disjoint, Finset.card_singleton, add_left_inj, h_rhs0, h_rhs, h_lhs1, h_lhs,
      h_rhs1, h_lhs_e, h_rhs_e, h_rhs0_e]
    convert goal_e

/-
theorem hyperedge_totalsize_deletion_contraction_none {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2)
  [DecidablePred F.sets] (hx_hyperedge_not : ¬ F.sets (F.ground \ {x})) :
  total_size_of_hyperedges F.toSetFamily + (F.ground.card - 1)=
  total_size_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily  +
  total_size_of_hyperedges (IdealDeletion.contraction F.toSetFamily x hx gcard) :=
  by
    calc
      (total_size_of_hyperedges F.toSetFamily) + (F.ground.card - 1)
          = total_size_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard)  +
            total_size_of_hyperedges (IdealDeletion.contraction F.toSetFamily x hx gcard) + degree F.toSetFamily x + (F.ground.card - 1) := by
             rw [hyperedge_totalsize_deletion_contraction F x hx gcard]
      _   = total_size_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily  +
            total_size_of_hyperedges (IdealDeletion.contraction F.toSetFamily x hx gcard) + degree F.toSetFamily x + (F.ground.card - 1) := by

    --lemma contraction_total_size (F : SetFamily α) [DecidablePred F.sets] (x : α)
    --(hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2) :
    --total_size_of_hyperedges (Mathematics.contraction F x hx gcard) =
    --  ((Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)).sum (λ s => Finset.card s - 1)

    --lemma sum_of_size_eq_degree_plus_contraction_sum (F : SetFamily α) (v : α)
    --(hg : F.ground.card ≥ 2) [DecidablePred F.sets] :
    --(Finset.filter (λ s => F.sets s ∧ v ∈ s) (Finset.powerset F.ground)).sum Finset.card =
    --degree F v + (Finset.filter (λ s => ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v) (Finset.powerset (F.ground.erase v))).sum Finset.card

    --lemma sum_partition_by_v (F : SetFamily α) (v : α) [DecidablePred F.sets] :
    --total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ v ∈ s,
    --                                 inc_ground := λ s hs => F.inc_ground s (hs.1) } +
    --total_size_of_hyperedges { F with sets := λ s => F.sets s ∧ v ∉ s,
    --                                 inc_ground := λ s hs => F.inc_ground s (hs.1) } =
    --total_size_of_hyperedges F

  -/

end Mathematics
