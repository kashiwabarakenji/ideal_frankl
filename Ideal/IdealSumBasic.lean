--IdealSumから呼ばれる補題を集めた。vを含めてhyperedgeの大きさの和を考えるのか、vを除いてhyperedgeの和を考えるのかを議論している。大きさの合計の関係の定理も。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Subtype
import Mathlib.Tactic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import LeanCopilot
--set_option maxHeartbeats 40000000
--set_option diagnostics true

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α]
--
--IdealSumから1回呼ばれている。vを含むか含まないかでtotalを分割。
omit [Fintype α] in
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
     ext
     simp
     simp only [Finset.mem_filter, Fsets, Fv, Fnv]--
     apply Iff.intro
     · intro a_1
       simp_all
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
    --goal Disjoint (Finset.filter (fun s => F.sets s ∧ v ∈ s) F.ground.powerset) (Finset.filter (fun s => F.sets s ∧ v ∉ s) F.ground.powerset)
      simp_all only [Fsets, Fv, Fnv]
      rw [Finset.disjoint_left]
      --theorem Finset.disjoint_left {α : Type u_1}  {s : Finset α}  {t : Finset α} :Disjoint s t ↔ ∀ ⦃a : α⦄, a ∈ s → a ∉ t
      intro a a_1
      rw [Finset.mem_filter,Finset.mem_powerset] at a_1 ⊢
      tauto
    )

  rw [←union_card_sum]
  rw [←disjoint_v]

--これはsubtypeでない。subtypeだとうまくいかなかったので、subtypeを使わないことを選択した。
--グローバルに定義されてしまっているが、このファイルの中でしか使っていない。
def domain00 (F : SetFamily α) (v : α) [DecidablePred F.sets] : Finset (Finset α) :=
  (Finset.powerset F.ground).filter (λ s => F.sets s ∧ v ∈ s)

def range00 (F : SetFamily α) (v : α) [DecidablePred F.sets] :  Finset (Finset α) :=
  (Finset.powerset (F.ground.erase v)).filter (λ s => ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v)

-- このファイルの下の方で使っている。
theorem bf_bijective (F : SetFamily α) (v : α) [DecidablePred F.sets](hxG: v ∈ F.ground) :
  Function.Bijective (λ (s : { S // S ∈ domain00 F v}) =>
    ⟨s.val.erase v, by
      dsimp [range00]
      simp_all only [domain00]
      obtain ⟨val, property⟩ := s
      simp_all only
      simp_all only [Finset.mem_filter, Finset.mem_powerset, domain00]
      obtain ⟨left, right⟩ := property
      obtain ⟨left_1, right⟩ := right
      apply And.intro
      · intro y hy
        simp only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at hy ⊢--
        obtain ⟨left_1, right_1⟩ := hy
        constructor
        exact left_1
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
    ⟩ : { S // S ∈ domain00 F v} → { S // S ∈ range00 F v}):=
  by
    constructor
    --1. 関数が単射であることを証明
    -- goal Function.Injective fun s ↦ ⟨(↑s).erase x, ⋯⟩
    · dsimp [Function.Injective]
      -- goal ∀ ⦃a₁ a₂ : { S // S ∈ Finset.filter (fun s ↦ F.sets s ∧ x ∈ s) F.ground.powerset }⦄,
      --⟨(↑a₁).erase x, ⋯⟩ = ⟨(↑a₂).erase x, ⋯⟩ → a₁ = a₂
      intro a₁ a₂ h
      have h_erase : (a₁.val).erase v = (a₂.val).erase v := by
       simpa using h
      let a1p := a₁.property
      dsimp [domain00] at a1p
      rw [Finset.mem_filter] at a1p
      let a2p := a₂.property
      dsimp [domain00] at a2p
      rw [Finset.mem_filter] at a2p

      obtain ⟨_, _, a₁_x⟩ := a1p
      obtain ⟨_, _, a₂_x⟩ := a2p
      have eq_goal: a₁.val = a₂.val := by
       exact (Ideal.erase_inj_of_mem a₁_x a₂_x).mp h_erase
      exact Subtype.eq eq_goal

    -- 2. 関数が全射であることを証明
    -- goal Function.Surjective fun s ↦ ⟨(↑s).erase x, ⋯⟩
    · dsimp [Function.Surjective]
      intro b
      -- goal ∃ a, ⟨(↑a).erase x, ⋯⟩ = b
      -- 単に値だけでなく、propertyも同時に満たす必要がある。valの値とpropertyを満たすことを同時に示す。
      -- goal ⟨(↑b).erase x, ⋯⟩ = b
      let bp:= b.property
      dsimp [range00] at bp
      rw [Finset.mem_filter] at bp
      obtain ⟨b_g, b_sets, b_v⟩ := bp
      let original := b.val ∪ {v}
      --originalが、domain00に属することを示す。
      have bpro: original ∈ domain00 F v:= by
        simp_all only [domain00]
        simp_all only [Finset.mem_powerset, Finset.mem_filter, Finset.mem_union,and_true, Finset.mem_singleton, or_true, original]--
        obtain ⟨val, property⟩ := b
        obtain ⟨b_left, right⟩ := b_v
        obtain ⟨right_1, right_2⟩ := right
        simp_all only
        subst right_2
        have v_in_b: v ∈ b_sets := by
          simp_all only [right_1]
        have b_eq: b_sets.erase v ∪ {v} = b_sets := by
          exact (Ideal.erase_insert b_sets v v_in_b)
        rw [b_eq]
        constructor
        --goal b_sets ⊆ F.ground
        have b_sets_ground: b_sets ⊆ F.ground := by
          apply subset_of_erase_subset v_in_b hxG b_g

        simp_all only
        exact b_left

    --goal: ∃ a, ⟨(↑a).erase x, ⋯⟩ = b
      use ⟨original, bpro⟩
      simp_all only [Finset.mem_powerset, original]
      simp_all only [and_self]
      obtain ⟨val, property⟩ := b
      obtain ⟨left, right⟩ := b_v
      obtain ⟨left_1, right⟩ := right
      simp_all only [Subtype.mk.injEq]
      simp_all only [Finset.mem_filter, domain00]--
      subst right
      obtain ⟨_, _⟩ := bpro
      ext1 a
      constructor
      · intro h
        simp_all only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]--
        simp_all only [ne_eq]
        obtain ⟨left_3, right_1⟩ := h
        simp_all only [not_false_eq_true, true_and, or_false]--
      · intro h
        simp_all only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
        simp_all only [ne_eq, not_false_eq_true, true_and]--
        simp only [or_false]


--omit [Nonempty α] in
lemma f_mem_range00 (F : SetFamily α) (v : α) [DecidablePred F.sets]
  (s : Finset α) (hs : s ∈ domain00 F v) : s.erase v ∈ range00 F v := by
  simp [range00]
  simp_all only [domain00]
  simp [domain00] at hs
  obtain ⟨left, right⟩ := hs
  obtain ⟨left_1, right⟩ := right
  apply And.intro
  · intro y hy
    simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]--
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
/-
-- s.val.erase v が range00 に属することを示す補題 subtype版
--omit [Nonempty α] in
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

--def f_total (F : SetFamily α) (v : α) [DecidablePred F.sets] (s : { S // S ∈ domain00 F v }) : { S // S ∈ range00 F v } := ⟨s.val.erase v, f_mem_range00_sub F v s⟩

--subtypeバージョン 結局sum_bijの時は、subtypeバージョンはうまくいかないということがわかったので、使わなかった。
def f_wrapped_sub (F : SetFamily α) (v : α) [DecidablePred F.sets]
  (s : { S // S ∈ domain00 F v }) : { T // T ∈ range00 F v } :=
  ⟨s.val.erase v, f_mem_range00_sub F v s⟩
-/

--非subtypeバージョン
def f_wrapped (F : SetFamily α) (v : α) [DecidablePred F.sets]
  (s : Finset α) (_ : s ∈ domain00 F v) : Finset α :=
  s.erase v


--f_wrappedのなかに単射の証拠がはいってなくて、bf_bijectiveのなかなので、困る。
--omit [Nonempty α] in
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

  apply (Ideal.erase_inj_of_mem v_in_a1 v_in_a2).mp
  exact h

lemma surjective_f_wrapped (F : SetFamily α) (v : α) [DecidablePred F.sets] (hvG: v ∈ F.ground)
  (b : Finset α) (hb : b ∈ range00 F v) :
  ∃ a, ∃ ha : a ∈ domain00 F v, f_wrapped F v a ha = b :=
by
  have bij_sur := (bf_bijective F v hvG).2
  rw [Function.Surjective] at bij_sur

  -- `bij_sur` に基づいてサブタイプ `b` に対する結果を展開
  obtain ⟨a, ha⟩ := bij_sur ⟨b, hb⟩
  -- `a` と `ha` を `f_wrapped` に適用して全射性を証明
  use a.val
  use a.property
  --refine ⟨a.val, a.property, _⟩
  have : f_wrapped F v a.val a.property = b := by
    simp [f_wrapped]
    simp_all only [ Subtype.mk.injEq]
  exact this

--IdealSumから呼ばれている。vを含むhyperedgeからvを取り除いたものを集めても数は同じ。
lemma card_equal (F : SetFamily α) (v : α) [DecidablePred F.sets](hvG: v ∈ F.ground) :
  (Finset.filter (λ s => F.sets s ∧ v ∈ s) (Finset.powerset F.ground)).card =
  (Finset.filter (λ s => ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v) (Finset.powerset (F.ground.erase v))).card :=
by

  let bij_inj := injective_f_wrapped F v hvG
  let bij_sur := surjective_f_wrapped F v hvG

  --subtypeを用いる方法では結局うまくいかなさそう。
  --let Fincard_sub := @Finset.card_bij (Finset α) (Finset α) (domain00 F v) (range00 F v) (f_wrapped_sub F v)
  let Fincard := @Finset.card_bij (Finset α) (Finset α) ( domain00 F v) (range00 F v) (f_wrapped F v) (f_mem_range00 F v) bij_inj bij_sur
  exact Fincard

--(vを含むhyperedgeの大きさ-1)の和は、vを含むhyperedgeをH-vを動かして作った集合族の大きさの和に等しい。
--次の定理sum_of_size_eq_degree_plus_contraction_sumで使う補題。
lemma sum_equal (F : SetFamily α) (v : α) [DecidablePred F.sets] :
  (Finset.filter (λ s => F.sets s ∧ v ∈ s) (Finset.powerset F.ground)).sum (λ s => Finset.card s - 1) =
  (Finset.filter (λ s => ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v) (Finset.powerset (F.ground.erase v))).sum Finset.card :=
by
  apply Finset.sum_bij (λ s _ => s.erase v)

  --値域に入っているか。
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

  -- 単射性
  · intro s hs t ht h
    simp only [Finset.mem_filter] at hs ht
    apply (Ideal.erase_inj_of_mem hs.2.2 ht.2.2).mp
    exact h

  -- 全射性
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

--vのを含むhyperedgeの大きさの和は、vの次数とvを含むhyperedgeからvを削除した大きさの和に等しい。IdealSumで3回呼ばれている。
lemma sum_of_size_eq_degree_plus_contraction_sum (F : SetFamily α) (v : α)
 [DecidablePred F.sets] :
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
    rw [Finset.mem_filter] at a
    simp only [Finset.one_le_card]
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
    simp_all

  rw [degree_eq]

  -- 5. 残りの和の等価性を示す
  rw [sum_equal]
  rfl

--IdealSumから3回ぐらい呼ばれる。xを含むhyperedgeの数と、xを除いたhyperedgeの数が等しい。上のcard_equalと違って、サイズの合計を議論。
lemma sumbij (F : SetFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) :
  let domain00 : Finset (Finset α):= (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)
  let range00 : Finset (Finset α) := (Finset.powerset (F.ground.erase x)).filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x)
  domain00.sum Finset.card = range00.sum Finset.card + range00.card:=
  by
   let domain0 :Finset (Finset α):= (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)
   let range0 :Finset (Finset α):= (Finset.powerset (F.ground.erase x)).filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x)

   let f := λ (s : Finset α) => Finset.card s
   let g := λ (s : Finset α) => (Finset.card s) + 1

   let i := (λ (s:Finset α) (_: s ∈ domain0) => s.erase x)

   -- 写像の値が終域に含まれることの証明 うまくいっているのか。
   have hi: ∀ s ∈ domain0, s.erase x ∈ range0 :=
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

   -- 写像が単射であることの証明
   have inj: ∀ (a₁ : Finset α) (ha₁ : a₁ ∈ domain0) (a₂ : Finset α) (ha₂ : a₂ ∈ domain0),
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
         exact (Ideal.erase_inj_of_mem h1 h2).mp h

   -- 写像が全射であることの証明
   have surj0: ∀ s ∈ range0, ∃H ∈ domain0, s = H.erase x :=
      by
        intros s hs
        simp only [Finset.mem_filter, Finset.mem_powerset] at hs
        dsimp [range0] at hs
        rw [Finset.mem_filter] at hs
        obtain ⟨H, hH1, hH2, hH3⟩ := hs.2

        use s ∪ {x}
        constructor
        -- goal s ∪ {x} ∈ range0
        · dsimp [range0]
          rw [Finset.mem_filter]
          simp_all
          --H.erase x ∪ {x} ⊆ F.ground ∧ F.sets (H.erase x ∪ {x})
          constructor

          · have s2: s ∪ {x} ⊆ (F.ground.erase x)∪{x} := by
              --simp_all only [true_and]
              subst hH3
              -- x ∈ w ∧ s = w.erase x
              gcongr
              exact hs.1

            have s3: (F.ground.erase x)∪{x} = F.ground := by
              apply Ideal.erase_insert F.ground x hx

            rw [s3] at s2
            -- hH1; F.sets H
            -- hH3: s = H.erase x
            have s5: s ∪ {x} = H := by
              rw [hH3]
              -- goal H.erase x ∪ {x} = H
              exact (Ideal.erase_insert H x hH2)
            have he: H.erase x ∪ {x} = H:= by
              exact (Ideal.erase_insert H x hH2)

            rw [he]
            rw [←s5]
            exact s2 --s ∪ {x} ⊆ F.ground
            --goal F.sets H
          · rw [←hH3]
            --s5と同じだがすこーぷが違う。
            have HS: H = s ∪ {x} := by
              rw [hH3]
              --goal H = H.erase x ∪ {x}
              --#check Ideal.erase_insert H x hH2
              exact (Ideal.erase_insert H x hH2).symm
            rw [←HS]
            exact hH1
        --goal  s = (s ∪ {x}).erase x
        · have s4: x ∉ s := by
            subst hH3
            simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]--
          exact (Ideal.union_erase_singleton s x s4).symm
   have surj:  ∀ b ∈ range0, ∃ a, ∃ (ha : a ∈ domain0), (fun s hs ↦ s.erase x) a ha = b :=
        by
          dsimp [range0,domain0]
          dsimp [range0,domain0] at surj0
          simp
          simp at surj0
          intro b hb c hc d hd
          let index4o := (surj0 b hb c hc d hd)
          obtain ⟨H, hH1, hH2, hH3⟩ := index4o
          tauto

   have h_comm0: ∀ (a : Finset α) (_ : a ∈ domain0),
        Finset.card a = Finset.card (a.erase x) + 1 :=
      by
        intros a ha
        dsimp [domain0] at ha
        simp only [Finset.mem_filter, Finset.mem_powerset] at ha

        -- `ha` より `x ∈ a` が成り立つことはすでに分かっている
        have hx : x ∈ a := by
          exact ha.2.2
        rw [Finset.card_erase_of_mem hx]

        simp_all

        have c0: Finset.card a >= 1 := by
          apply Nat.one_le_of_lt
          apply Finset.card_pos.mpr
          exact ⟨x, hx⟩
        simp_all only [Nat.sub_add_cancel]

   have h_comm: ∀ (a : Finset α) (ha : a ∈ domain0), f a = g ((fun s _ ↦ s.erase x) a ha) :=
      by
        dsimp [f, g]
        dsimp [domain0]
        dsimp [domain0] at h_comm0
        simp
        simp at h_comm0
        intro a ha b hb
        simp [range0, ha, h_comm0, hb]

        have hx : x ∈ a := by
          exact hb
        have c0: Finset.card a >= 1 := by
          apply Nat.one_le_of_lt
          apply Finset.card_pos.mpr
          exact ⟨x, hx⟩
        simp_all only [ Nat.sub_add_cancel]

   let ap := @Finset.sum_bij _ _ _ _ domain0 range0 f g i hi  inj surj h_comm

   -- sum の分配と簡単な変形
   dsimp [domain0, range0] at ap ⊢

   have domain_eq: domain0 = (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s) :=
      by rfl
   have range_eq: range0 = (Finset.powerset (F.ground.erase x)).filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) :=
      by rfl
   rw [←domain_eq,←range_eq] at ap
   have ghave: g = λ s => (Finset.card s) + 1 := by rfl
   rw [ghave] at ap
   rw [Finset.sum_add_distrib] at ap

   simp at ap
   rw [ap]

   end Ideal
