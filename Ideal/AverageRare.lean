--平均rareであれば、rareな頂点が存在することに関する定理。メインの「ideal集合族は平均abundantにならない」定理の証明とは関係ない。
--Ideal集合族でなく、一般の集合族に関する定理。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import LeanCopilot

namespace Ideal

variable {α : Type} [DecidableEq α]
--fintype α は必要なところにつける。

--このページで使う補題等。BasicLemmasに移動しても良い。
omit [DecidableEq α] in
lemma decarte (A : Finset α) (B : Finset (Finset α)) (a : α) (b : Finset α)
  (ha : a ∈ A) (hb : b ∈ B) : (a, b) ∈ A.product B := by
  -- `Finset.product` の定義に基づき、`(a, b)` は `A.product B` に属する
  apply Finset.mem_product.2 ⟨ha, hb⟩

omit [DecidableEq α] in
lemma decarter {α:Type}{a:α}{b:Finset α} (A : Finset α) (B : Finset (Finset α)) (h:(a, b) ∈ A.product B)
  : a ∈ A ∧ b ∈ B := by
  -- `Finset.product` の定義に基づき、`(a, b)` は `A.product B` に属する
  exact Finset.mem_product.1 h

lemma sum_nonneg_of_nonneg {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℤ) (h : ∀ x ∈ s, 0 ≤ f x) :
  0 ≤ s.sum f := by
  apply Finset.sum_induction
  · intro a b a_1 a_2
    omega
  · simp_all only [le_refl]
  intro x a
  simp_all only

lemma sum_posi_of_posi {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℤ) (nonempty: s ≠ ∅) (h : ∀ x ∈ s, 0 < f x) :
  0 < s.sum f := by
  obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty nonempty
  -- sの非空性からa ∈ s を取得
  have h_pos : 0 < f a := h a ha
  rw [Finset.sum_eq_add_sum_diff_singleton ha]
  --simp_all only [ne_eq, singleton_subset_iff, sum_sdiff_eq_sub, sum_singleton, add_sub_cancel, gt_iff_lt]
  apply add_pos_of_pos_of_nonneg
  · exact h_pos
  · apply sum_nonneg_of_nonneg
    intros x hx
    simp_all only [ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
    obtain ⟨left, _⟩ := hx
    exact (h x left).le

lemma sum_nonpos_exists_nonpos {α : Type} [DecidableEq α] (s : Finset α)(nonempty: s ≠ ∅) (f : α → ℤ) (h : s.sum f ≤ 0) :
  ∃ x ∈ s, f x ≤ 0 := by
  by_contra h1
  -- 仮定を否定して、すべての x に対して f x > 0 であると仮定
  push_neg at h1

  have h_pos : 0 < s.sum f := by
    let sn := sum_posi_of_posi s (λ x => f x) nonempty (by simp_all [h1])
    apply lt_of_le_of_ne
    apply le_trans
    on_goal 2 => {exact sn
    }
    simp_all only [zero_add, Int.reduceLE]
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [le_refl]
    simp [a] at sn
  simp_all only [ne_eq]
  exact not_le_of_lt h_pos h

-------
-- FGは台集合。F.groundに相当。ちょっと一般化して証明した補題。
-- 定義: FG.product hyperedges は hyperedges のデカルト積
def FG_product (FG :Finset α) (hyperedges : Finset (Finset α))[DecidableEq hyperedges] : Finset (α × Finset α) :=
  FG.product hyperedges

-- 定義: filtered_product は FG.product hyperedges の中で p.1 ∈ p.2 を満たすペアの集合
def filtered_product (FG :Finset α) (hyperedges : Finset (Finset α)) [DecidableEq hyperedges]: Finset (α × Finset α)   :=
  (FG_product FG hyperedges).filter (λ p => (p.1 ∈ p.2))

-- 補題: x ⊆ FG であれば, FG.filter (λ a, a ∈ x ) = x  すぐ下で使っている。
lemma filter_eq_self_of_subset (FG : Finset α) (x : Finset α)
  (h_subset : x ⊆ FG) :
  FG.filter (λ a => a ∈ x ) = x := by
  ext a
  constructor
  intro ha
  rw [Finset.mem_filter] at ha
  exact ha.right

  intro ha
  rw [Finset.mem_filter]
  constructor
  exact h_subset ha
  simp_all only

-- 主な補題: 任意の x ∈ hyperedges に対して、フィルタリング後のカード数は x.card に等しい。最後で使っている。
lemma filter_card_eq_x_card (FG :Finset α) (hyperedges : Finset (Finset α))
  (x : Finset α) (hx : x ∈ hyperedges)(hFG: ∀ s:Finset α, s ∈ hyperedges → s ⊆ FG) :
  ((filtered_product FG hyperedges).filter (λ ab => ab.2 = x)).card = x.card :=
  by
    let domain := FG.filter (λ a => a ∈ x )
    let range := (filtered_product FG hyperedges).filter (λ ab => ab.2 = x )

    -- 補題の適用: x ⊆ FG
    have h_subset : x ⊆ FG := by
      simp_all only

    -- 補題を使って domain = x
    have h_domain_eq : domain = x := filter_eq_self_of_subset FG x h_subset

    -- マッピング関数 f : domain → range を定義
    let i: (a:α) → (a ∈ domain) → (α × Finset α) := fun a _ => (a, x)

    have hi: ∀ (a: α) (ha:a ∈ domain), i a ha ∈ range :=
      by
        intros a ha
        simp_all only [Finset.mem_filter, and_true, i, domain, range]
        simp_all only [Finset.mem_filter, domain]
        dsimp [filtered_product]
        dsimp [FG_product]
        simp_all only [Finset.mem_filter, and_true]
        have h1: a ∈ FG := by
          apply hFG
          on_goal 2 => {exact ha
          }
          · simp_all only
        --#check decarte FG hyperedges a x h1 hx
        exact decarte FG hyperedges a x h1 hx

    -- 関数 i が単射であることを示す
    have inj : ∀ (a: α) (ha:a ∈ domain) (b: α) (hb: b ∈ domain), ((i a ha) = (i b hb)) → a = b :=
      by
        intro a ha b hb hH
        simp_all only [Prod.mk.injEq, and_true, i, domain]

    have surj : ∀ p ∈ range, ∃ a, ∃ (h : a ∈ domain), i a h = p :=
      by
         dsimp [range]
         dsimp [filtered_product]
         dsimp [FG_product]
         dsimp [domain]
         intro p a
         simp_all only [Finset.mem_filter, exists_prop, domain, i]--
         obtain ⟨fst, snd⟩ := p
         obtain ⟨left, right⟩ := a
         obtain ⟨_, right_1⟩ := left
         subst right
         simp_all only [Prod.mk.injEq, and_true, exists_eq_right]

    have bij := Finset.card_bij i hi inj surj
    rw [Finset.card_filter]
    simp [range]
    rw [← bij]
    rw [h_domain_eq]

--これも動くが、AとBを明示的に引数にしたものをset3として作った。今は使ってない。
lemma card_sum_over_fst_eq_card_sum_over_snd_set2 {α: Type u}[DecidableEq α][Fintype α] (C : Finset (α × (Finset α))) :
  C.card = Finset.univ.sum (fun a => (C.filter (fun ab => (ab.1 = a))).card) ∧
  C.card = Finset.univ.sum (fun b => (C.filter (fun ab => ab.snd = b)).card) := by
     -- 第一の等式: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
  constructor
  · -- 第一の等式の証明: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
    apply @Finset.card_eq_sum_card_fiberwise (α × Finset α) α _ (fun ab => ab.fst) C Finset.univ
    intro x _
    simp_all only [Finset.mem_univ]
  · -- 第二の等式の証明: C.card = Σ_{b ∈ B} |C.filter (fun ab => ab.snd = b)|
    apply @Finset.card_eq_sum_card_fiberwise (α × Finset α) (Finset α) _ (fun ab => ab.snd) C Finset.univ
    intros ab _
    exact Finset.mem_univ ab.snd

  --univを使わない改良版。下で使っている。
  lemma card_sum_over_fst_eq_card_sum_over_snd_set3 {α: Type}[DecidableEq α][Fintype α] (A: Finset α)(B:Finset (Finset α))(C : Finset (α × (Finset α))):
  C ⊆ (A.product B) →
  C.card = A.sum (fun a => (C.filter (fun ab => (ab.1 = a))).card) ∧
  C.card = B.sum (fun b => (C.filter (fun ab => ab.2 = b)).card) := by
     -- 第一の等式: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
  intro hC

  constructor
  · -- 第一の等式の証明: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
    apply @Finset.card_eq_sum_card_fiberwise (α × Finset α) α _ (fun ab => ab.fst) C A
    intro x _
    have hh: (x.1,x.2) ∈ A.product B := by
      apply hC
      simp_all only [Prod.mk.eta]
    --#check @decarter α x.1 x.2 A B hh
    exact (@decarter α x.1 x.2 A B hh).1

  · -- 第二の等式の証明: C.card = Σ_{b ∈ B} |C.filter (fun ab => ab.snd = b)|
    apply @Finset.card_eq_sum_card_fiberwise (α × Finset α) (Finset α) _ (fun ab => ab.snd) C B
    intro x a
    have hh: (x.1,x.2) ∈ A.product B := by
      apply hC
      simp_all only [Prod.mk.eta]
    exact (@decarter α x.1 x.2 A B hh).2
    --
theorem sum_cardinality_eq [Fintype α](FG : Finset α) [DecidableEq FG] (hyperedges : Finset (Finset α))(fground: ∀s:Finset α, s ∈ hyperedges → s ⊆ FG) :
  FG.sum (fun x => (FG.powerset.filter (fun s => s ∈ hyperedges ∧ x ∈ s)).card) =
  hyperedges.sum (fun s => s.card) := by

    let convert_product_to_pair  (fa : Finset α) (fb : Finset (Finset α)) : Finset (α × Finset α) :=
      fa.product fb |>.map (Function.Embedding.refl (α × Finset α))
    let pairs := (convert_product_to_pair FG hyperedges) |>.filter (λ p => (p.1 ∈ p.2 : Prop))
    have inc: pairs ⊆ (FG.product hyperedges) := by
      simp_all only [Finset.map_refl, Finset.filter_subset, pairs, convert_product_to_pair]

    have h1 := @card_sum_over_fst_eq_card_sum_over_snd_set3 α _ _ FG hyperedges pairs inc

    have h2 := h1.1
    rw [h1.2] at h2

    dsimp [pairs] at h2
    simp at h2
    dsimp [convert_product_to_pair] at h2
    simp at h2
    --h2の右辺と、ゴールの左辺が近い形。ただし、Finset alphaと、FGの差がある。
    have equal:  ∑ x ∈ FG, (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product hyperedges))).card = ∑ x ∈ FG, (Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset).card := by
        apply Finset.sum_congr
        simp_all only [Finset.mem_univ]
        --goal  ∑ x : α, (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product hyperedges))).card = ∑ x ∈ FG, (Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset).card
        intro x _

        -- x in Finset.univとか、hyperedges ⊆ Finset.univは使いそう。
        have equal_card :
          (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product hyperedges))).card =
          (Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset).card :=
        by
          -- 対応関数の定義
          let i := (λ s (_ : s ∈ Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset) => (x, s))

          -- 関数 `i` が右辺の要素を左辺に写像することを確認します
          have hi : ∀ (s : Finset α) (hs : s ∈ Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset),
            i s hs ∈ Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product hyperedges)) := by
            intros s hs
            simp only [i, Finset.mem_filter, and_true, eq_self_iff_true, Prod.fst]
            --subst fground
            simp_all only [Finset.mem_filter,  and_true, pairs, convert_product_to_pair]
            obtain ⟨_, right⟩ := hs
            simp_all only [Finset.mem_powerset]
            have xinFG: x ∈ FG := by
              simp_all only
            exact decarte FG hyperedges x s xinFG right.1

          -- 関数 `i` が単射であることを確認します
          have i_inj : ∀ (a₁ : Finset α) (ha₁ : a₁ ∈ Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset)
            (a₂ : Finset α) (ha₂ : a₂ ∈ Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset),
            i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ := by
              intros a₁ a₂ ha₁ ha₂ h
              injection h with h1

          have i_surj : ∀ (b : α × Finset α)
            (_ : b ∈ Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product hyperedges))),
            ∃ a, ∃ (ha : a ∈ Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset), i a ha = b :=
            by
              intro b hb
              simp_all only [ Finset.mem_filter, exists_prop, i, pairs,convert_product_to_pair]
              obtain ⟨fst, snd⟩ := b
              obtain ⟨left, right⟩ := hb
              obtain ⟨left_1, right_1⟩ := left
              apply Finset.mem_product.mp at left_1
              subst right
              simp_all only [Prod.mk.injEq, true_and, exists_eq_right, and_true]--
              simp_all only [Finset.mem_powerset]

          -- card_bij を適用して左辺と右辺のカードの数が一致することを示します
          exact (Finset.card_bij i hi i_inj i_surj).symm
        exact equal_card

    --goal ∑ x ∈ FG, (Finset.filter (fun s => s ∈ hyperedges ∧ x ∈ s) FG.powerset).card = ∑ s ∈ hyperedges, s.card
    rw [←equal]
    rw [←h2]

    apply Finset.sum_congr
    exact rfl
    intro x hx
    exact filter_card_eq_x_card FG hyperedges x hx fground

--Definitionsに移しても良い。
noncomputable def normalized_degree {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x: α): ℤ :=
  2 * (degree F x:Int) - (number_of_hyperedges F:Int)

-- 型全体に対する合計
lemma sum_univ {α : Type} [DecidableEq α] [Fintype α] (f : α → ℕ) : ∑ x : α, f x = ∑ x in Finset.univ, f x := by
  simp_all only

--頂点ごとに足すか、hyperedgeの大きさを足すかで等しい。
theorem double_count {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α):
  total_size_of_hyperedges F = ∑ x in F.ground, degree F x := by
  rw [total_size_of_hyperedges]
  dsimp [degree]
  simp_all
  symm

  let Fsets := F.ground.powerset.filter (λ s => F.sets s)
  have ffground: (∀ s ∈ Fsets, s ⊆ F.ground) := by
    intros s hs
    dsimp [Fsets] at hs
    rw [Finset.mem_filter] at hs
    exact F.inc_ground s hs.2

  let tmp := sum_cardinality_eq F.ground Fsets ffground
  have subs: ∀ s:Finset α,s ∈ Fsets  ↔ (F.sets s ∧ s ⊆ F.ground) := by
    dsimp [Fsets]
    intro s
    symm
    rw [Finset.mem_filter]
    apply Iff.intro
    intro h
    constructor
    rw [Finset.mem_powerset]
    exact h.2
    exact h.1

    intro h
    rw [Finset.mem_powerset] at h
    exact ⟨h.2, h.1⟩

  have subs2:∑ x ∈ F.ground, (Finset.filter (fun s => s ∈ Fsets ∧ x ∈ s) F.ground.powerset).card = ∑ x ∈ F.ground, (Finset.filter (fun s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s) F.ground.powerset).card := by
    apply Finset.sum_congr
    swap
    intro x _
    simp only [subs]

    congr

  have subs3: ∑ x ∈ F.ground, (Finset.filter (fun s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s) F.ground.powerset).card =  ∑ x ∈ F.ground, (Finset.filter (fun s => (F.sets s) ∧ x ∈ s) F.ground.powerset).card := by
    apply Finset.sum_congr
    swap
    intro x _
    let i:= (λ s (_ : s ∈ F.ground.powerset.filter (λ s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s)) => s)
    have hi: ∀ s (hs : s ∈ F.ground.powerset.filter (λ s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s)), i s hs ∈ F.ground.powerset.filter (λ s => F.sets s ∧ x ∈ s) := by
      intros s hs
      simp_all only [i]
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_filter]
      constructor
      exact hs.1
      obtain ⟨left, right⟩ := hs.2
      constructor
      exact left.1
      exact right

    have inj : ∀ (a₁ : Finset α) (ha₁:a₁ ∈ F.ground.powerset.filter (λ s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s))
      (a₂ : Finset α) (ha₂: a₂ ∈ F.ground.powerset.filter (λ s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s)), i a₁ ha₁ = i a₂ ha₂→ a₁ = a₂ := by
      intros a₁ _ a₂ _ h
      simp_all only [i]
    have surj : ∀ p ∈ F.ground.powerset.filter (λ s => F.sets s ∧ x ∈ s), ∃ a, ∃ (ha : a ∈ F.ground.powerset.filter (λ s => (F.sets s ∧ s ⊆ F.ground) ∧ x ∈ s)), i a ha = p := by
      intro p hp
      simp_all only [i]
      rw [Finset.mem_filter] at hp
      let hpp := hp.1
      rw [Finset.mem_powerset] at hpp
      use p
      constructor
      swap
      rw [Finset.mem_filter]
      constructor
      rw [Finset.mem_powerset]
      exact hpp
      constructor
      constructor
      exact hp.2.1
      exact hpp
      exact hp.2.2
      congr

    exact Finset.card_bij i hi inj surj
    congr

  rw [subs2] at tmp
  rw [subs3] at tmp

  exact tmp

--平均rareであれば、少なくとも一つの頂点がrareである。このファイルのメイン定理。
theorem average_rare_vertex  [Nonempty α][Fintype α](F:SetFamily α) :
  normalized_degree_sum F <= 0 → ∃ x ∈ F.ground, normalized_degree F x <= 0 := by

  have ndegrees: normalized_degree_sum F = ∑ x in F.ground, (normalized_degree F x) := by
    calc
      normalized_degree_sum F
      = ((∑ x in F.ground, (degree F x)):Int) * 2 - (number_of_hyperedges F * F.ground.card:ℤ) := by
        rw [normalized_degree_sum]
        have h2 := double_count F
        simp
        rw [h2]
        simp
    _ = ((∑ x in F.ground, (2*(degree F x)) : ℤ) - (F.ground.card * number_of_hyperedges F) : ℤ) := by
        ring_nf
        symm
        ring_nf
        simp_all only [add_right_inj]
        rw [Finset.sum_mul]
    _ = (∑ x in F.ground, (2*(degree F x)):Int) - (∑ x in F.ground,1)*((number_of_hyperedges F):Int):= by
        simp_all only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (∑ x in F.ground, (2*(degree F x)):Int) - (∑ x in F.ground,(number_of_hyperedges F):Int):= by
        simp_all only [Finset.sum_const]
        simp_all only [nsmul_eq_mul, mul_one]
    _ = ∑ x in F.ground, ((2*(degree F x):Int) - (number_of_hyperedges F):Int) := by
        rw [←Finset.sum_sub_distrib]
    _ = ∑ x in F.ground, (normalized_degree F x) := by
        simp only [normalized_degree]

  rw [ndegrees]
  intro h
  have h3 := sum_nonpos_exists_nonpos F.ground
   (by
    apply Finset.nonempty_iff_ne_empty.mp
    exact F.nonempty_ground
   )
   (fun (x:α) => (2 * degree F x) - (number_of_hyperedges F)) h

  obtain ⟨x, hx, h4⟩ := h3
  dsimp [normalized_degree] at h4
  use x
  constructor
  exact hx
  dsimp [normalized_degree]
  exact h4

end Ideal
