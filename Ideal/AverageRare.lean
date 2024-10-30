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
--variable {α : Type*} [DecidableEq α][Fintype α]

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

-- 定義: FG.product filtered_powerset は filtered_powerset のデカルト積
def FG_product (FG :Finset α) (filtered_powerset : Finset (Finset α))[DecidableEq filtered_powerset] : Finset (α × Finset α) :=
  FG.product filtered_powerset

-- 定義: filtered_product は FG.product filtered_powerset の中で p.1 ∈ p.2 を満たすペアの集合
def filtered_product (FG :Finset α) (filtered_powerset : Finset (Finset α)) [DecidableEq filtered_powerset]: Finset (α × Finset α)   :=
  (FG_product FG filtered_powerset).filter (λ p => (p.1 ∈ p.2))

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

-- 主な補題: 任意の x ∈ filtered_powerset に対して、
-- フィルタリング後のカード数は x.card に等しい。最後で使っている。
lemma filter_card_eq_x_card (FG :Finset α) (filtered_powerset : Finset (Finset α))
  (x : Finset α) (hx : x ∈ filtered_powerset)(hFG: ∀ s:Finset α, s ∈ filtered_powerset → s ⊆ FG) :
  ((filtered_product FG filtered_powerset).filter (λ ab => ab.2 = x)).card = x.card :=
  by
    -- フィルタリング後の集合 S は { (a, x) | a ∈ x }
    let range := (filtered_product FG filtered_powerset).filter (λ ab => ab.2 = x )

    -- 対応する集合 T は { a | a ∈ x }
    let domain := FG.filter (λ a => a ∈ x )

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
        --#check decarte FG filtered_powerset a x h1 hx
        exact decarte FG filtered_powerset a x h1 hx

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
         simp_all only [Finset.mem_filter, and_true, Prod.mk.injEq, implies_true, exists_prop, and_self_left, domain,
           i, range]
         obtain ⟨fst, snd⟩ := p
         obtain ⟨left, right⟩ := a
         obtain ⟨_, right_1⟩ := left
         subst right
         simp_all only [Prod.mk.injEq, and_true, exists_eq_right]

    have bij := Finset.card_bij i hi inj surj
    simp_all only [Finset.mem_filter, and_true, Prod.mk.injEq, implies_true, exists_prop, and_imp, Prod.forall,
      exists_eq_right, domain, i, range]

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
--variable (A B : Type) (C : Finset (A × B))[DecidableEq A][DecidableEq B] [Fintype A] [Fintype B][DecidableEq C]
--variable (a : A)
--#check C.filter (fun ab => (ab.1 = a))

--これは使ってない。
lemma card_sum_over_fst_eq_card_sum_over_snd {α β : Type} [DecidableEq α][DecidableEq β] [Fintype α] [Fintype β] (C : Finset (α × β)) :
  C.card = Finset.univ.sum (fun a => (C.filter (fun ab => (ab.1 = a))).card) ∧
  C.card = Finset.univ.sum (fun b => (C.filter (fun ab => ab.snd = b) : Finset (α × β)).card) := by
     -- 第一の等式: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
  constructor
  · -- 第一の等式の証明: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
    apply @Finset.card_eq_sum_card_fiberwise (α × β) α _ (fun ab => ab.fst) C Finset.univ
    intro x _
    simp_all only [Finset.mem_univ]
  · -- 第二の等式の証明: C.card = Σ_{b ∈ B} |C.filter (fun ab => ab.snd = b)|
    apply @Finset.card_eq_sum_card_fiberwise  (α × β) β _ (fun ab => ab.snd) C Finset.univ
    intros ab _
    exact Finset.mem_univ ab.snd

--これは使ってない。
lemma card_sum_over_fst_eq_card_sum_over_snd_set {α: Type}{β:Finset α} [DecidableEq β][Fintype β] (C : Finset (β × (Finset β))) :
  C.card = Finset.univ.sum (fun a => (C.filter (fun ab => (ab.1 = a))).card) ∧
  C.card = Finset.univ.sum (fun b => (C.filter (fun ab => ab.snd = b)).card) := by
  constructor
  · -- 第一の等式の証明: C.card = Σ_{a ∈ A} |C.filter (fun ab => ab.fst = a)|
    apply @Finset.card_eq_sum_card_fiberwise (β × Finset β) β _ (fun ab => ab.fst) C Finset.univ
    intro x _
    simp_all only [Finset.mem_univ]
  · -- 第二の等式の証明: C.card = Σ_{b ∈ B} |C.filter (fun ab => ab.snd = b)|
    apply @Finset.card_eq_sum_card_fiberwise (β × Finset β) (Finset β) _ (fun ab => ab.snd) C Finset.univ
    intros ab _
    exact Finset.mem_univ ab.snd

--これを使っている。Finset univじゃなくて、これでも動くが、AとBを明示的に引数にしたものをset3として作った。
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

  --univを使わない改良版。こちらを使いたい。
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
-- FG = groundの仮定をなんとかしたい。Finset.univとなっているところを全部、FGに変えることでなんとかしたい。後日行う。
theorem sum_cardinality_eq [Fintype α](FG : Finset α) [DecidableEq FG] (filtered_powerset : Finset (Finset α))  (fground: FG = Finset.univ) :
  FG.sum (fun x => (FG.powerset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s)).card) =
  filtered_powerset.sum (fun s => s.card) := by
    have hFG: ∀ s:Finset α, s ∈ filtered_powerset → s ⊆ FG := by
      intros s _
      subst fground
      simp_all only [Finset.subset_univ]

    let convert_product_to_pair  (fa : Finset α) (fb : Finset (Finset α)) : Finset (α × Finset α) :=
      fa.product fb |>.map (Function.Embedding.refl (α × Finset α))
    let pairs := (convert_product_to_pair FG filtered_powerset) |>.filter (λ p => (p.1 ∈ p.2 : Prop))
    have inc: pairs ⊆ (FG.product filtered_powerset) := by
      simp_all only [Finset.map_refl, Finset.filter_subset, pairs, convert_product_to_pair]


    have h1 := @card_sum_over_fst_eq_card_sum_over_snd_set2 α _ _ pairs
    --have h1 := @card_sum_over_fst_eq_card_sum_over_snd_set3 α _ _ FG filtered_powerset pairs inc
    --#check h1
    have h2 := h1.1
    rw [h1.2] at h2

    dsimp [pairs] at h2
    simp at h2
    dsimp [convert_product_to_pair] at h2
    simp at h2
    --h2の右辺と、ゴールの左辺が近い形。ただし、Finset alphaと、FGの差がある。証明が完了している。
    have equal:  ∑ x : α, (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card = ∑ x ∈ FG, (Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) FG.powerset).card := by
        apply Finset.sum_congr
        simp_all only [Finset.mem_univ]
        --goal  ∑ x : α, (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card = ∑ x ∈ FG, (Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) FG.powerset).card
        intro x _

        simp_all only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_self, and_true, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_filter]
        -- x in Finset.univとか、filtered_powerset ⊆ Finset.univは使いそう。
        have equal_card :
          (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (Finset.univ.product filtered_powerset))).card =
          (Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset).card :=
        by
          -- 左辺のフィルタの数を右辺のフィルタの数と一致させるため、card_bij を使って両者の対応を構築します

          -- 対応関数を定義します
          let i := (λ s (_ : s ∈ Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset) => (x, s))

          -- 関数 `i` が右辺の要素を左辺に写像することを確認します
          have hi : ∀ (s : Finset α) (hs : s ∈ Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset),
            i s hs ∈ Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (Finset.univ.product filtered_powerset)) := by
            intros s hs
            simp only [i, Finset.mem_filter, and_true, eq_self_iff_true, Prod.fst]
            subst fground
            simp_all only [Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.map_refl,
              Finset.filter_subset, and_self, and_true, pairs, convert_product_to_pair]
            obtain ⟨left, _⟩ := hs
            exact Finset.mem_product.mpr ⟨Finset.mem_univ x, left⟩

          -- 関数 `i` が単射であることを確認します
          have i_inj : ∀ (a₁ : Finset α) (ha₁ : a₁ ∈ Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset)
            (a₂ : Finset α) (ha₂ : a₂ ∈ Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset),
            i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ := by
              intros a₁ a₂ ha₁ ha₂ h
              injection h with h1
              --goal (Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (Finset.univ.product filtered_powerset))).card =
              -- (Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset).card

          -- 関数 `i` が全射であることを確認します
          have i_surj : ∀ (b : α × Finset α)
            (_ : b ∈ Finset.filter (fun ab => ab.1 = x) (Finset.filter (fun p => p.1 ∈ p.2) (Finset.univ.product filtered_powerset))),
            ∃ a, ∃ (ha : a ∈ Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) Finset.univ.powerset), i a ha = b :=
            by
              intro b hb
              subst fground
              simp_all only [Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and, and_self, and_true,
                and_imp, Prod.mk.injEq, implies_true, Finset.map_refl, Finset.filter_subset, exists_prop, i, pairs,
                convert_product_to_pair]
              obtain ⟨fst, snd⟩ := b
              obtain ⟨left, right⟩ := hb
              obtain ⟨left_1, right_1⟩ := left
              apply Finset.mem_product.mp at left_1
              subst right
              simp_all only [Prod.mk.injEq, true_and, exists_eq_right, and_true]

          -- card_bij を適用して左辺と右辺のカードの数が一致することを示します
          exact (Finset.card_bij i hi i_inj i_surj).symm
        exact equal_card

    --goal ∑ x ∈ FG, (Finset.filter (fun s => s ∈ filtered_powerset ∧ x ∈ s) FG.powerset).card = ∑ s ∈ filtered_powerset, s.card
    rw [←equal]
    --rw [fground] at h2
    rw [←h2]

    have h_zero : ∀ x : Finset α, x ∈ Finset.univ \ filtered_powerset → (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card = 0 :=
      by
        intro x hx
        rw [Finset.card_eq_zero]
        by_contra h_contra
        push_neg at h_contra
        let tmp_set := (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset)))
        have h_nonempty:tmp_set.Nonempty := by
          subst fground
          simp_all only [Finset.map_refl, Finset.filter_subset, Finset.powerset_univ, and_self, ne_eq, pairs,
            convert_product_to_pair]
          rwa [Finset.nonempty_iff_ne_empty]
        obtain ⟨ab, hab⟩ := h_nonempty
        have h_snd : ab.2 = x := by
          subst fground
          simp_all only [Finset.map_refl, Finset.filter_subset, Finset.powerset_univ, and_self, ne_eq,
            Finset.mem_filter, pairs, convert_product_to_pair, tmp_set]
        have hx : x ∈ filtered_powerset := by
          simp_all only [Finset.map_refl, Finset.filter_subset, Finset.powerset_univ, and_self, ne_eq,
            Finset.mem_filter, pairs, convert_product_to_pair]
          simp [tmp_set] at hab
          obtain ⟨hab_left,_⟩ := hab.1
          apply Finset.mem_product.mp at hab_left
          rw [h_snd] at hab_left
          subst h_snd fground
          simp_all only [not_true_eq_false]
        subst h_snd fground
        simp_all only [not_true_eq_false]
        simp_all only [Finset.mem_sdiff, Finset.mem_univ, not_true_eq_false, and_false]

    let filtered_powerset_comp := (Finset.univ : Finset (Finset α)) \ filtered_powerset

    have disjoint_lem: Disjoint filtered_powerset filtered_powerset_comp:= by
      subst fground
      simp_all only [Finset.map_refl, Finset.filter_subset, Finset.powerset_univ, and_self, Finset.card_eq_zero,
        pairs, convert_product_to_pair, filtered_powerset_comp]
      exact disjoint_sdiff_self_right

    have union_lem: (Finset.univ : Finset (Finset α)) = filtered_powerset ∪ filtered_powerset_comp := by
      subst fground
      simp_all only [Finset.map_refl, Finset.filter_subset, Finset.powerset_univ, and_self, Finset.card_eq_zero,
        Finset.union_sdiff_self_eq_union, Finset.right_eq_union, Finset.subset_univ, filtered_powerset_comp, pairs,
        convert_product_to_pair]

    have sum_zero: ∑ x in filtered_powerset_comp, (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card = 0 := by
      apply Finset.sum_eq_zero
      dsimp [filtered_powerset_comp]
      exact h_zero

    have sum_union: ∑ x in (Finset.univ : Finset (Finset α)), (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card
      = ∑ x in filtered_powerset, (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card
      + ∑ x in filtered_powerset_comp, (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card:= by
      rw [←Finset.sum_union disjoint_lem]
      rw [union_lem]

    have equal_lem: ∑ x : Finset α,(Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card = ∑ x in filtered_powerset, (Finset.filter (fun ab => ab.2 = x) (Finset.filter (fun p => p.1 ∈ p.2) (FG.product filtered_powerset))).card := by
      rw [sum_union]
      rw [sum_zero]
      simp

    rw [equal_lem]
    apply Finset.sum_congr
    exact rfl
    intro x hx
    exact filter_card_eq_x_card FG filtered_powerset x hx hFG

noncomputable def normalized_degree {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x: α): ℤ :=
  2 * degree F x - number_of_hyperedges F

theorem double_count {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x: α):
  total_size_of_hyperedges F = ∑ x, degree F x := by
  rw [total_size_of_hyperedges]
  dsimp [degree]
  simp_all
  symm
  --xが全体の和になっているが、F.groundだけの和にしたほうがいいかも。そうしないと下でマッチしてくれない。
  have rewrite: ∑ x : α, (Finset.filter (fun s => F.sets s ∧ x ∈ s) F.ground.powerset).card = ∑ x ∈ F.ground, (Finset.filter (fun s => F.sets s ∧ x ∈ s) F.ground.powerset).card := by
    have rewrite_lem: x ∈ Finset.univ \ F.ground → (Finset.filter (fun s => F.sets s ∧ x ∈ s) F.ground.powerset).card = 0 := by
      intro a
      simp_all only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.card_eq_zero]
      ext
      simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.not_mem_empty, iff_false, not_and]
      intro a_1 a_2
      apply Aesop.BuiltinRules.not_intro
      intro a_3
      exact a (a_1 a_3)
    simp_all only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.card_eq_zero]
    --#check Finset.sum_eq_zeroやsum_unionなどを使う。disjoint性も証明。
    --simp [Finset.sum_union] at rewrite
    --apply Finset.sum_eq_zero
    sorry

  --#check  @sum_cardinality_eq
  let MyType := {x : α // x ∈ F.ground}  -- αの代わりにMyTypeを使用
  have h_ft : Fintype MyType := inferInstance
  let Fsets := (Finset.powerset (Finset.univ : Finset MyType)).filter (λ s => F.sets (s.map (Function.Embedding.subtype _)))
  #check @sum_cardinality_eq MyType _ _ _ _ Fsets rfl
  --sorry


theorem average_rare_vertex [Fintype α](F:SetFamily α) :
  normalized_degree_sum F <= 0 → ∃ x ∈ F.ground, normalized_degree F x < 0 := by
  sorry

end Ideal