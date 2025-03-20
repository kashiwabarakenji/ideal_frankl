import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Tactic
import LeanCopilot
import rooted.CommonDefinition
import rooted.GeneralLemma
--import rooted.ClosureMinors

variable {α : Type} [Fintype α] [DecidableEq α]

-- (_: f1.ground ∩ f2.ground = ∅ )
def DirectProduct  (f1 f2: SetFamily α): SetFamily α :=
{
  ground := f1.ground ∪ f2.ground,
  sets := fun s => ∃s1:Finset α, ∃ s2 :Finset α, f1.sets s1 ∧ f2.sets s2 ∧ s = s1 ∪ s2
  inc_ground := by
    intro s hs
    obtain ⟨s1, s2, hs1, hs2, hs⟩ := hs
    intro x hx
    rw [Finset.mem_union]
    rw [hs] at hx
    rw [Finset.mem_union] at hx
    cases hx
    case intro.inl hx1 =>
      left
      exact f1.inc_ground s1 hs1 hx1
    case intro.inr hx2 =>
      right
      exact f2.inc_ground s2 hs2 hx2

  nonempty_ground := by
    rcases f1.nonempty_ground with ⟨x, hx⟩
    simp_all only [Finset.union_nonempty]
    tauto
}

--(_: f1.ground ∩ f2.ground = ∅ )
instance direct_Product_decidable(f1 f2: SetFamily α) [DecidablePred f1.sets] [DecidablePred f2.sets]:
  DecidablePred (DirectProduct f1 f2).sets :=
by
  rw [DirectProduct]
  simp_all only [exists_and_left]
  infer_instance

lemma direct_Product_number_of_hyperedges (f1 f2: SetFamily α) (disj: f1.ground ∩ f2.ground = ∅ ) [DecidablePred f1.sets] [DecidablePred f2.sets]:
  (DirectProduct f1 f2).number_of_hyperedges = f1.number_of_hyperedges * f2.number_of_hyperedges :=
by
  let S1 := Finset.filter (fun s => f1.sets s) (f1.ground.powerset)
  let S2 := Finset.filter (fun s => f2.sets s) (f2.ground.powerset)
  let SP := Finset.filter
    (fun s => ∃ (x y : Finset α), f1.sets x ∧ f2.sets y ∧ s = x ∪ y)
    ((f1.ground ∪ f2.ground).powerset)

  /- 2. それぞれが number_of_hyperedges と対応することを確認 -/
  have eq_nhe_f1 : f1.number_of_hyperedges = Int.ofNat S1.card := by
    unfold SetFamily.number_of_hyperedges
    rfl

  have eq_nhe_f2 : f2.number_of_hyperedges = Int.ofNat S2.card := by
    unfold SetFamily.number_of_hyperedges
    rfl

  have eq_nhe_prod : (DirectProduct f1 f2).number_of_hyperedges = Int.ofNat SP.card := by
    unfold SetFamily.number_of_hyperedges
    simp_all only [Int.ofNat_eq_coe, exists_and_left, Nat.cast_inj, S1, S2, SP]
    congr 1
    simp [DirectProduct]

  /-
    3. 写像 (s1, s2) ↦ s1 ∪ s2 を構成。
       「S1 × S2」と「SP」のあいだで全単射を示すために
       Finset.card_bij を使う。
  -/
  let toUnion : (p : Finset α × Finset α) → p ∈ S1.product S2 → Finset α := fun p _ => p.1 ∪ p.2

  /-
    3a. hi : toUnion が S1×S2 の要素を SP の要素へ送る
         p.1, p.2 がそれぞれ f1.sets, f2.sets のフィルタを通るなら
         p.1 ∪ p.2 は SP の定義(∃ x y, ...)を満たす
  -/
  have hi : ∀ (p : Finset α × Finset α), (h:p ∈ S1.product S2) → toUnion p h ∈ SP := by
    intro p
    --simp at p
    dsimp [toUnion]
    obtain ⟨pval, pprop⟩ := p
    intro h
    simp_all [SP, S2, S1, toUnion]
    obtain ⟨left, right⟩ := h
    obtain ⟨left, right_1⟩ := left
    obtain ⟨left_1, right⟩ := right
    apply And.intro
    · gcongr
    · exact ⟨_, right_1, _, right, rfl⟩

  /-
    3b. i_inj : 単射性
         (s1 ∪ s2) = (s1' ∪ s2') ⇒ (s1,s2)=(s1',s2')
         台集合 disjoint ⇒ s1 = (s1 ∪ s2) ∩ f1.ground
  -/
  have i_inj : ∀ (p₁ p₂ : Finset α × Finset α),
      (h1:p₁ ∈ S1.product S2) →
      (h2:p₂ ∈ S1.product S2) →
      toUnion p₁ h1 = toUnion p₂ h2 →
      p₁ = p₂ := by
    intro p₁ p₂ hp₁ hp₂ heq
    -- p₁ = (x1, x2), p₂ = (y1, y2) と分解
    cases p₁ with
    | mk x1 x2 =>
      have hx1 : f1.sets x1 := by
        simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, SP, S2, S1, toUnion]
        simp_all only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset, SP, S2, S1,
          toUnion]
      have hx2: f2.sets x2 := by
        simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, SP, S2, S1, toUnion]
        simp_all only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset, and_true,
          SP, S2, S1, toUnion]
      cases p₂ with
      | mk y1 y2 =>
        -- x1 ∪ x2 = y1 ∪ y2
        rw [Finset.product] at hp₁ hp₂
        simp at hp₁ hp₂
        dsimp [SProd.sprod] at hp₁ hp₂
        have hy1 : f1.sets y1 := by
          simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
            Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, Finset.filter_val, Multiset.mem_product,
            Multiset.mem_filter, Finset.mem_val, and_true, SP, S2, S1, toUnion]
        have hy2: f2.sets y2 := by
          simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
            Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, Finset.filter_val, Multiset.mem_product,
            Multiset.mem_filter, Finset.mem_val, and_true, SP, S2, S1, toUnion]
        dsimp [toUnion] at heq
        have xy1: x1 = y1 :=
        by
          have :(x1 ∪ x2) ∩ f1.ground = x1 := by
            ext a
            simp
            simp_all [SP, S2, S1, toUnion]
            apply Iff.intro
            · intro a_1
              obtain ⟨left, right⟩ := a_1
              cases left with
              | inl h => simp_all only [SP, S2, S1, toUnion]
              | inr h_1 => --h_1とrightとdisjで矛盾。
                have : a ∈ f2.ground := by
                  obtain ⟨left, right_1⟩ := hp₁
                  obtain ⟨left_1, right_2⟩ := hp₂
                  apply right_1
                  simp_all only [SP, S2, S1, toUnion]
                have ain: a ∈ f1.ground ∩ f2.ground := by
                  exact Finset.mem_inter_of_mem right this
                exfalso
                simp_all only [Finset.not_mem_empty, SP, S2, S1, toUnion]
            · intro a_1
              simp_all only [true_or, true_and, SP, S2, S1, toUnion]
              have : x1 ⊆ f1.ground := by
                exact f1.inc_ground x1 hx1
              exact this a_1
          have : (y1 ∪ y2) ∩ f1.ground = y1 := by
            ext a
            simp
            simp_all [SP, S2, S1, toUnion]
            apply Iff.intro
            · intro a_1
              obtain ⟨left, right⟩ := a_1
              cases left with
              | inl h => simp_all only [SP, S2, S1, toUnion]
              | inr h_1 =>
                have : a ∈ f2.ground := by
                  obtain ⟨left, right_1⟩ := hp₁
                  obtain ⟨left_1, right_2⟩ := hp₂
                  apply right_2
                  simp_all only [SP, S2, S1, toUnion]
                have ain: a ∈ f1.ground ∩ f2.ground := by
                  exact Finset.mem_inter_of_mem right this
                exfalso
                simp_all only [Finset.not_mem_empty, SP, S2, S1, toUnion]

            · intro a_1
              simp_all only [true_or, true_and, SP, S2, S1, toUnion]
              have : y1 ⊆ f1.ground := by
                exact f1.inc_ground y1 hy1
              rename_i this_1
              subst this_1
              simp_all only [true_and, Finset.inter_subset_right, SP, S2, S1, toUnion]
              apply this
              simp_all only [SP, S2, S1, toUnion]
          simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
            Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, Finset.filter_val, Multiset.mem_product,
            Multiset.mem_filter, Finset.mem_val, and_true, SP, S2, S1, toUnion]
        have xy2: x2 = y2 := by
          have :(x1 ∪ x2) ∩ f2.ground = x2 := by
            ext a
            simp
            simp_all [SP, S2, S1, toUnion]
            apply Iff.intro
            · intro a_1
              obtain ⟨left, right⟩ := a_1
              cases left with
              | inl h =>
                have ain2: a ∈ f2.ground := by
                  subst xy1
                  simp_all only [SP, S2, S1, toUnion]
                have ain1: a ∈ f1.ground := by
                  obtain ⟨left, right_1⟩ := hp₁
                  subst xy1
                  simp_all only [SP, S2, S1, toUnion]
                  exact left h
                have ain: a ∈ f1.ground ∩ f2.ground := by
                  exact Finset.mem_inter_of_mem ain1 ain2
                exfalso
                simp_all only [Finset.not_mem_empty, SP, S2, S1, toUnion]
              | inr h_1 => simp_all only [SP, S2, S1, toUnion]
            · intro a_1
              simp_all only [true_or, true_and, SP, S2, S1, toUnion]
              have : x2 ⊆ f2.ground := by
                  exact f2.inc_ground x2 hx2
              subst xy1
              simp_all only [or_true, true_and, SP, S2, S1, toUnion]
              obtain ⟨left, right⟩ := hp₁
              apply right
              simp_all only [SP, S2, S1, toUnion]

          have : (y1 ∪ y2) ∩ f2.ground = y2 := by
            ext a
            simp
            simp_all [SP, S2, S1, toUnion]
            apply Iff.intro
            · intro a_1
              obtain ⟨left, right⟩ := a_1
              cases left with
              | inl h =>
                have ain1: a ∈ f1.ground := by
                  obtain ⟨left, right_1⟩ := hp₁
                  subst xy1 this
                  simp_all only [Finset.inter_subset_right, SP, S2, S1, toUnion]
                  apply left
                  simp_all only [SP, S2, S1, toUnion]
                have ain2: a ∈ f2.ground := by
                  subst xy1 this
                  simp_all only [Finset.inter_subset_right, and_true, SP, S2, S1, toUnion]
                have : a ∈ f1.ground ∩ f2.ground := by
                  exact Finset.mem_inter_of_mem ain1 ain2
                exfalso
                simp_all only [Finset.not_mem_empty, SP, S2, S1, toUnion]

              | inr h_1 =>
                simp_all only [SP, S2, S1, toUnion]
            · intro a_1
              subst xy1 this
              simp_all only [Finset.inter_subset_right, and_true, or_true, true_and, SP, S2, S1, toUnion]
              exact hp₂ a_1
          subst xy1
          simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
            Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, Finset.filter_val, Multiset.mem_product,
            Multiset.mem_filter, Finset.mem_val, and_true, and_self, SP, S2, S1, toUnion]
        subst xy2 xy1
        simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, Finset.filter_val, Multiset.mem_product,
          Multiset.mem_filter, Finset.mem_val, and_true, and_self, SP, S2, S1, toUnion]

  have i_inj2: ∀ (a₁ : Finset α × Finset α) (ha₁ : a₁ ∈ S1.product S2) (a₂ : Finset α × Finset α) (ha₂ : a₂ ∈ S1.product S2),
  toUnion a₁ ha₁ = toUnion a₂ ha₂ → a₁ = a₂ := by
    intros a₁ ha₁ a₂ ha₂ h
    exact i_inj a₁ a₂ ha₁ ha₂ h

  /-
    3c. i_surj : 全射性
         任意の s ∈ SP をとると，s = x ∪ y となる (f1.sets x ∧ f2.sets y) がある
         そこから (x,y) ∈ S1×S2 かつ toUnion(x,y)=s を構成
  -/
  have i_surj : ∀ s ∈ SP, ∃ p ∈ S1.product S2, (h:p ∈ S1.product S2) → toUnion p h = s := by
    intro s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨hs_power, ⟨x, y, hx_sets, hy_sets, rfl⟩⟩ := hs
    -- x, y は f1.sets, f2.sets を満たすので S1, S2 の要素となる
    have x_in : x ∈ S1 := by
      rw [Finset.mem_filter]
      constructor
      . apply Finset.mem_powerset.mpr (f1.inc_ground x hx_sets)
      . exact hx_sets
    have y_in : y ∈ S2 := by
      rw [Finset.mem_filter]
      constructor
      . apply Finset.mem_powerset.mpr (f2.inc_ground y hy_sets)
      . exact hy_sets
    -- では (x,y) ∈ S1×S2
    have xy_in : (x, y) ∈ S1.product S2 := by
      rw [Finset.product]
      simp
      dsimp [SProd.sprod]
      --dsimp [Multiset.product]
      simp
      constructor
      · exact x_in
      · exact y_in

    exact Filter.frequently_principal.mp fun a => a xy_in (congrFun rfl)

  have i_surj2 : ∀ b ∈ SP, ∃ a, ∃ (ha : a ∈ S1.product S2), toUnion a ha = b := by
    intros b hb
    let sj := i_surj b hb
    obtain ⟨p, hp, h⟩ := sj
    exact BEx.intro p hp (h hp)
  /-
    4. Finset.card_bij を適用して |S1 × S2| = |SP| を示す
       (card_product で |S1×S2| = |S1| * |S2| )
  -/
  have eq_card : (S1.product S2).card = SP.card := by
    apply Finset.card_bij toUnion
    . exact hi      --  (a) toUnion p は SP の要素
    . exact i_inj2   --  (b) 単射性
    . exact i_surj2  --  (c) 全射性
  /-
    5. 以上より最終的に (DirectProduct f1 f2).number_of_hyperedges
       = f1.number_of_hyperedges * f2.number_of_hyperedges
       を示す
  -/
  calc
    (DirectProduct f1 f2).number_of_hyperedges
    = Int.ofNat SP.card := eq_nhe_prod
    _ = Int.ofNat (S1.card * S2.card) := by
      dsimp [SProd.sprod]
      rw [← eq_card]
      norm_cast
      dsimp [Finset.product]
      rw [←Finset.card_product]
    _ = (Int.ofNat S1.card) * (Int.ofNat S2.card) := by simp
    _ = f1.number_of_hyperedges * f2.number_of_hyperedges := by
      rw [← eq_nhe_f1, ← eq_nhe_f2]

lemma direct_Product_total_size_of_hyperedges (f1 f2: SetFamily α) (disj: f1.ground ∩ f2.ground = ∅ ) [DecidablePred f1.sets] [DecidablePred f2.sets]:
  (DirectProduct f1 f2).total_size_of_hyperedges = f1.total_size_of_hyperedges * f2.number_of_hyperedges + f1.number_of_hyperedges * f2.total_size_of_hyperedges := by
  let S1 := Finset.filter (fun s => f1.sets s) (f1.ground.powerset)
  let S2 := Finset.filter (fun s => f2.sets s) (f2.ground.powerset)
  let SP := Finset.filter
    (fun s => ∃ (x y : Finset α), f1.sets x ∧ f2.sets y ∧ s = x ∪ y)
    ((f1.ground ∪ f2.ground).powerset)

  /- 2. total_size_of_hyperedges と Finset.sum の関係をそれぞれ明示 -/
  have eq_ts_f1 : f1.total_size_of_hyperedges = Int.ofNat (S1.sum (fun s => s.card)) := by
    unfold SetFamily.total_size_of_hyperedges
    rfl

  have eq_ts_f2 : f2.total_size_of_hyperedges = Int.ofNat (S2.sum (fun s => s.card)) := by
    unfold SetFamily.total_size_of_hyperedges
    rfl

  have eq_ts_dp : (DirectProduct f1 f2).total_size_of_hyperedges
                    = Int.ofNat (SP.sum (fun s => s.card)) := by
    unfold SetFamily.total_size_of_hyperedges
    dsimp [DirectProduct]
    dsimp [SP]
    simp_all only [Int.ofNat_eq_coe, Nat.cast_sum, exists_and_left, SP, S1, S2]


  /- 3. SP と (S1 × S2) の間で全単射を作り、sum_bij で「要素ごとの s.card の総和」を一致させる -/

  /- 写像 toUnion: (x,y) ↦ x ∪ y --/
  let toUnion := (fun (p : Finset α × Finset α) (hp : p ∈ S1.product S2) =>
      -- 前の定理で使っていたように、p.1 ∪ p.2 を返す
      p.1 ∪ p.2
    )
    --fun (p : Finset α × Finset α) => p.1 ∪ p.2

  /-
    sum_bij に使うための条件を順番に示していく。

    sum_bij の形は:
    ```
    Finset.sum_bij (S1×S2) SP
      (λ p => (p.1 ∪ p.2).card)            -- 左集合をわたすときの「値」
      (λ s => s.card)                      -- 右集合をわたすときの「値」
      toUnion                              -- 写像 (p₁ : S1×S2) → SP の要素
      (…hi…) (…inj…) (…surj…)
    ```
  -/

  --------------------------------------------------------------------------------
  -- (a) 「写像 toUnion が S1×S2 の要素を SP の要素に送る」
  --------------------------------------------------------------------------------
  have hi : ∀ (p : Finset α × Finset α), (h:p ∈ S1.product S2) → toUnion p h ∈ SP := by
    intro p
    --simp at p
    dsimp [toUnion]
    obtain ⟨pval, pprop⟩ := p
    intro h
    simp_all [SP, S2, S1, toUnion]
    obtain ⟨left, right⟩ := h
    obtain ⟨left, right_1⟩ := left
    obtain ⟨left_1, right⟩ := right
    apply And.intro
    · gcongr
    · exact ⟨_, right_1, _, right, rfl⟩

  --------------------------------------------------------------------------------
  -- (b) 単射性:
  --     (x1 ∪ x2 = y1 ∪ y2) ⇒ (x1,x2)=(y1,y2) を示す。
  --     disj: f1.ground ∩ f2.ground = ∅ により、x1 = (x1 ∪ x2) ∩ f1.ground 等が成り立つ。
  --------------------------------------------------------------------------------
  have i_inj : ∀ (p₁ p₂ : Finset α × Finset α),
      (h1:p₁ ∈ S1.product S2) →
      (h2:p₂ ∈ S1.product S2) →
      toUnion p₁ h1 = toUnion p₂ h2 →
      p₁ = p₂ := by
    intro p₁ p₂ hp₁ hp₂ heq
    -- p₁ = (x1, x2), p₂ = (y1, y2) と分解
    cases p₁ with
    | mk x1 x2 =>
      have hx1 : f1.sets x1 := by
        simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, SP, S2, S1, toUnion]
        simp_all only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset, SP, S2, S1,
          toUnion]
      have hx2: f2.sets x2 := by
        simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, SP, S2, S1, toUnion]
        simp_all only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset, and_true,
          SP, S2, S1, toUnion]
      cases p₂ with
      | mk y1 y2 =>
        -- x1 ∪ x2 = y1 ∪ y2
        rw [Finset.product] at hp₁ hp₂
        simp at hp₁ hp₂
        dsimp [SProd.sprod] at hp₁ hp₂
        have hy1 : f1.sets y1 := by
          simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
            Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, Finset.filter_val, Multiset.mem_product,
            Multiset.mem_filter, Finset.mem_val, and_true, SP, S2, S1, toUnion]
        have hy2: f2.sets y2 := by
          simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
            Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, Finset.filter_val, Multiset.mem_product,
            Multiset.mem_filter, Finset.mem_val, and_true, SP, S2, S1, toUnion]
        dsimp [toUnion] at heq
        have xy1: x1 = y1 :=
        by
          have :(x1 ∪ x2) ∩ f1.ground = x1 := by
            ext a
            simp
            simp_all [SP, S2, S1, toUnion]
            apply Iff.intro
            · intro a_1
              obtain ⟨left, right⟩ := a_1
              cases left with
              | inl h => simp_all only [SP, S2, S1, toUnion]
              | inr h_1 => --h_1とrightとdisjで矛盾。
                have : a ∈ f2.ground := by
                  obtain ⟨left, right_1⟩ := hp₁
                  obtain ⟨left_1, right_2⟩ := hp₂
                  apply right_1
                  simp_all only [SP, S2, S1, toUnion]
                have ain: a ∈ f1.ground ∩ f2.ground := by
                  exact Finset.mem_inter_of_mem right this
                exfalso
                simp_all only [Finset.not_mem_empty, SP, S2, S1, toUnion]
            · intro a_1
              simp_all only [true_or, true_and, SP, S2, S1, toUnion]
              have : x1 ⊆ f1.ground := by
                exact f1.inc_ground x1 hx1
              exact this a_1
          have : (y1 ∪ y2) ∩ f1.ground = y1 := by
            ext a
            simp
            simp_all [SP, S2, S1, toUnion]
            apply Iff.intro
            · intro a_1
              obtain ⟨left, right⟩ := a_1
              cases left with
              | inl h => simp_all only [SP, S2, S1, toUnion]
              | inr h_1 =>
                have : a ∈ f2.ground := by
                  obtain ⟨left, right_1⟩ := hp₁
                  obtain ⟨left_1, right_2⟩ := hp₂
                  apply right_2
                  simp_all only [SP, S2, S1, toUnion]
                have ain: a ∈ f1.ground ∩ f2.ground := by
                  exact Finset.mem_inter_of_mem right this
                exfalso
                simp_all only [Finset.not_mem_empty, SP, S2, S1, toUnion]

            · intro a_1
              simp_all only [true_or, true_and, SP, S2, S1, toUnion]
              have : y1 ⊆ f1.ground := by
                exact f1.inc_ground y1 hy1
              rename_i this_1
              subst this_1
              simp_all only [true_and, Finset.inter_subset_right, SP, S2, S1, toUnion]
              apply this
              simp_all only [SP, S2, S1, toUnion]
          simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
            Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, Finset.filter_val, Multiset.mem_product,
            Multiset.mem_filter, Finset.mem_val, and_true, SP, S2, S1, toUnion]
        have xy2: x2 = y2 := by
          have :(x1 ∪ x2) ∩ f2.ground = x2 := by
            ext a
            simp
            simp_all [SP, S2, S1, toUnion]
            apply Iff.intro
            · intro a_1
              obtain ⟨left, right⟩ := a_1
              cases left with
              | inl h =>
                have ain2: a ∈ f2.ground := by
                  subst xy1
                  simp_all only [SP, S2, S1, toUnion]
                have ain1: a ∈ f1.ground := by
                  obtain ⟨left, right_1⟩ := hp₁
                  subst xy1
                  simp_all only [SP, S2, S1, toUnion]
                  exact left h
                have ain: a ∈ f1.ground ∩ f2.ground := by
                  exact Finset.mem_inter_of_mem ain1 ain2
                exfalso
                simp_all only [Finset.not_mem_empty, SP, S2, S1, toUnion]
              | inr h_1 => simp_all only [SP, S2, S1, toUnion]
            · intro a_1
              simp_all only [true_or, true_and, SP, S2, S1, toUnion]
              have : x2 ⊆ f2.ground := by
                  exact f2.inc_ground x2 hx2
              subst xy1
              simp_all only [or_true, true_and, SP, S2, S1, toUnion]
              obtain ⟨left, right⟩ := hp₁
              apply right
              simp_all only [SP, S2, S1, toUnion]

          have : (y1 ∪ y2) ∩ f2.ground = y2 := by
            ext a
            simp
            simp_all [SP, S2, S1, toUnion]
            apply Iff.intro
            · intro a_1
              obtain ⟨left, right⟩ := a_1
              cases left with
              | inl h =>
                have ain1: a ∈ f1.ground := by
                  obtain ⟨left, right_1⟩ := hp₁
                  subst xy1 this
                  simp_all only [Finset.inter_subset_right, SP, S2, S1, toUnion]
                  apply left
                  simp_all only [SP, S2, S1, toUnion]
                have ain2: a ∈ f2.ground := by
                  subst xy1 this
                  simp_all only [Finset.inter_subset_right, and_true, SP, S2, S1, toUnion]
                have : a ∈ f1.ground ∩ f2.ground := by
                  exact Finset.mem_inter_of_mem ain1 ain2
                exfalso
                simp_all only [Finset.not_mem_empty, SP, S2, S1, toUnion]

              | inr h_1 =>
                simp_all only [SP, S2, S1, toUnion]
            · intro a_1
              subst xy1 this
              simp_all only [Finset.inter_subset_right, and_true, or_true, true_and, SP, S2, S1, toUnion]
              exact hp₂ a_1
          subst xy1
          simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
            Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, Finset.filter_val, Multiset.mem_product,
            Multiset.mem_filter, Finset.mem_val, and_true, and_self, SP, S2, S1, toUnion]
        subst xy2 xy1
        simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, Finset.filter_val, Multiset.mem_product,
          Multiset.mem_filter, Finset.mem_val, and_true, and_self, SP, S2, S1, toUnion]

  have i_inj2: ∀ (a₁ : Finset α × Finset α) (ha₁ : a₁ ∈ S1.product S2) (a₂ : Finset α × Finset α) (ha₂ : a₂ ∈ S1.product S2),
  toUnion a₁ ha₁ = toUnion a₂ ha₂ → a₁ = a₂ := by
    intros a₁ ha₁ a₂ ha₂ h
    exact i_inj a₁ a₂ ha₁ ha₂ h

  --------------------------------------------------------------------------------
  -- (c) 全射性:
  --     任意の s ∈ SP をとると、s = x ∪ y で x ∈ S1, y ∈ S2 を構成できる
  --------------------------------------------------------------------------------
  --have surj : ∀ s ∈ SP, ∃ (p : Finset α × Finset α), p ∈ S1.product S2 ∧ toUnion p = s := by
  have i_surj : ∀ s ∈ SP, ∃ p ∈ S1.product S2, (h:p ∈ S1.product S2) → toUnion p h = s := by
    intro s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨hs_power, ⟨x, y, hx_sets, hy_sets, rfl⟩⟩ := hs
    -- x, y は f1.sets, f2.sets を満たすので S1, S2 の要素となる
    have x_in : x ∈ S1 := by
      rw [Finset.mem_filter]
      constructor
      . apply Finset.mem_powerset.mpr (f1.inc_ground x hx_sets)
      . exact hx_sets
    have y_in : y ∈ S2 := by
      rw [Finset.mem_filter]
      constructor
      . apply Finset.mem_powerset.mpr (f2.inc_ground y hy_sets)
      . exact hy_sets
    -- では (x,y) ∈ S1×S2
    have xy_in : (x, y) ∈ S1.product S2 := by
      rw [Finset.product]
      simp
      dsimp [SProd.sprod]
      --dsimp [Multiset.product]
      simp
      constructor
      · exact x_in
      · exact y_in

    exact Filter.frequently_principal.mp fun a => a xy_in (congrFun rfl)

  have i_surj2 : ∀ b ∈ SP, ∃ a, ∃ (ha : a ∈ S1.product S2), toUnion a ha = b := by
    intros b hb
    let sj := i_surj b hb
    obtain ⟨p, hp, h⟩ := sj
    exact BEx.intro p hp (h hp)

  /- 4. sum_bij を使って
       ∑(s in SP) s.card = ∑(p in S1×S2) (p.1 ∪ p.2).card
     を示す。
     ここで f s = s.card, g p = (p.1 ∪ p.2).card.
  -/

  have eq_sum :
    SP.sum (fun s => s.card)
    = (S1.product S2).sum (fun p => (p.1 ∪ p.2).card) := by
    -- Finset.sum_bij
    symm
    apply Finset.sum_bij toUnion hi i_inj2 i_surj2
    intros p hp
    dsimp [toUnion] at *
    -- Using that p.1 ⊆ f1.ground and p.2 ⊆ f2.ground along with disj: f1.ground ∩ f2.ground = ∅,
    -- we deduce p.1 ∩ p.2 = ∅ and so card (p.1 ∪ p.2) = p.1.card + p.2.card.

      -- 最後に、値部分 (f p) = (p.1 ∪ p.2).card, (f s) = s.card が一致するから OK

  /-
    5. 台集合が交わらない ⇒ (p.1 ∪ p.2).card = p.1.card + p.2.card.
       よって
       ∑(p in S1×S2) (p.1 ∪ p.2).card
       = ∑(p in S1×S2) (p.1.card + p.2.card)
       = (∑(x in S1) x.card)*|S2| + (∑(y in S2) y.card)*|S1|.
  -/
  have eq_disjoint_sum :
    (S1.product S2).sum (fun p => (p.1 ∪ p.2).card)
    = (S1.product S2).sum (fun p => p.1.card + p.2.card) := by
    -- 各 p で要素が共通しないため
    apply Finset.sum_congr rfl
    intro p p_in
    have hg_disj : p.1 ∩ p.2 = ∅ := by
      -- p.1 ⊆ f1.ground, p.2 ⊆ f2.ground かつ ground が素なため
      -- 実際には f1.sets x → x ⊆ f1.ground が仮定されている
      rw [Finset.product] at p_in
      simp at p_in
      dsimp [SProd.sprod] at p_in
      simp at p_in
      have hx1: f1.sets p.1 := by
        simp_all only [Int.ofNat_eq_coe, exists_and_left, Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_filter, Finset.mem_powerset, and_imp, Prod.forall, SP, S2, S1, toUnion]
      have hx2: f2.sets p.2 := by
        dsimp [S2] at p_in
        let p_in2 := p_in.2
        rw [Finset.mem_filter] at p_in2
        exact p_in2.2
      have hp1: p.1 ⊆ f1.ground := by
        exact f1.inc_ground p.1 hx1
      have hp2: p.2 ⊆ f2.ground := by
        exact f2.inc_ground p.2 hx2
      by_contra h_contra
      have h_contra2: ∃ a, a ∈ p.1 ∩ p.2 := by
        exact exists_mem_of_ne_empty (p.1 ∩ p.2) h_contra
      obtain ⟨a, ha⟩ := h_contra2
      rw [Finset.mem_inter] at ha
      have h: a ∈ f1.ground ∩ f2.ground := by
        apply Finset.mem_inter_of_mem
        exact hp1 ha.1
        exact hp2 ha.2
      rw [disj] at h
      exact Finset.not_mem_empty a h

    have hg_disj2 : Disjoint p.1 p.2:= by
      exact Finset.disjoint_iff_inter_eq_empty.mpr hg_disj


    -- 以上で (p.1 ∪ p.2).card = p.1.card + p.2.card
    let hue := Finset.card_union_eq_card_add_card.mpr hg_disj2
    rw [hue]


  have eq_sum_expand :
    (S1.product S2).sum (fun p => p.1.card + p.2.card)
    = (S1.sum (fun x => x.card)) * S2.card
    + (S2.sum (fun y => y.card)) * S1.card := by
    rw [Finset.sum_add_distrib]

    -- ここで ∑(p in S1×S2) f(p.1) = ∑(x in S1) f(x) * |S2|
    --               と同様に ∑(p in S1×S2) f(p.2) = …
    show ∑ x ∈ S1.product S2, x.1.card + ∑ x ∈ S1.product S2, x.2.card = (∑ x ∈ S1, x.card) * S2.card + (∑ y ∈ S2, y.card) * S1.card
    have h_left:  ∑ p ∈ S1.product S2, p.1.card = (S1.sum (fun x => x.card)) * S2.card := by
      -- これは前の定理で使ったものと同じ
      dsimp [Finset.product]
      calc
          ∑ p ∈ S1 ×ˢ S2, p.1.card
          = ∑ x ∈ S1, x.card * (∑ y ∈ S2, 1) := by
            -- 「x は固定, y を全列挙」形へ分解
            simp only [Finset.sum_const]
            rw [Finset.sum_product]
            congr
            ext x
            simp
            exact Nat.mul_comm S2.card x.card
         _ = (∑ x ∈ S1, x.card) * S2.card := by
            rw [Finset.sum_const]
            simp only [Nat.cast_sum, Finset.card_eq_sum_ones]
            simp
            exact Eq.symm (Finset.sum_mul S1 Finset.card S2.card)

    have h_right: ∑ p ∈ S1.product S2, p.2.card = (S2.sum (fun y => y.card)) * S1.card := by
      /- 同様に後半 -/
      dsimp [Finset.product]
      calc
        ∑ p ∈ (S1  ×ˢ S2), p.2.card
        = ∑ y ∈ S2, y.card * (∑ x ∈ S1, 1) := by
          simp only [Finset.sum_const]
          rw [Finset.sum_product]
          rw [Finset.sum_comm]
          congr
          ext yy
          simp
          exact Nat.mul_comm S1.card yy.card
      _ = (S2.sum (fun y => y.card)) * S1.card := by
        rw [Finset.sum_const]
        simp only [Nat.cast_sum, Finset.card_eq_sum_ones]
        simp
        exact Eq.symm (Finset.sum_mul S2 Finset.card S1.card)
    --dsimp [Finset.product]

    rw [h_left, h_right]


  /- 以上をまとめて、

     SP.sum (fun s => s.card)
     = (S1.product S2).sum (fun p => (p.1 ∪ p.2).card)
     = (S1.product S2).sum (fun p => p.1.card + p.2.card)
     = (∑(x in S1) x.card)*|S2| + (∑(y in S2) y.card)*|S1|.
  -/
  show (DirectProduct f1 f2).total_size_of_hyperedges =
  f1.total_size_of_hyperedges * f2.number_of_hyperedges + f1.number_of_hyperedges * f2.total_size_of_hyperedges
  rw [eq_ts_dp]
  rw [eq_sum]
  rw [eq_disjoint_sum]
  rw [eq_sum_expand]
  dsimp [DirectProduct, SetFamily.number_of_hyperedges, SetFamily.total_size_of_hyperedges]
  dsimp [S1, S2]
  simp
  rw [Int.mul_comm]

omit [Fintype α] in
lemma direct_product_ground_set (f1 f2: SetFamily α)  [DecidablePred f1.sets] [DecidablePred f2.sets]:
  (DirectProduct f1 f2).ground = f1.ground ∪ f2.ground := by
  ext a
  simp
  apply Iff.intro
  · intro a_1
    dsimp [DirectProduct] at a_1
    simp_all only [Finset.mem_union]
  · intro a_1
    dsimp [DirectProduct]
    simp_all only [Finset.mem_union]

omit [Fintype α] in
lemma direct_product_ground_set_card (f1 f2: SetFamily α) (disj: f1.ground ∩ f2.ground = ∅ ) [DecidablePred f1.sets] [DecidablePred f2.sets]:
  (DirectProduct f1 f2).ground.card = f1.ground.card + f2.ground.card := by
  rw [direct_product_ground_set f1 f2]
  rw [←Finset.card_union_add_card_inter]
  simp_all only [Finset.card_empty, add_zero]

lemma direct_Product_normalized_degree_sum (f1 f2: SetFamily α) (disj: f1.ground ∩ f2.ground = ∅ ) [DecidablePred f1.sets] [DecidablePred f2.sets]:
  (DirectProduct f1 f2).normalized_degree_sum = f2.number_of_hyperedges*f1.normalized_degree_sum + f1.number_of_hyperedges * f2.normalized_degree_sum := by
  let S1 := Finset.filter (fun s => f1.sets s) (f1.ground.powerset)
  let S2 := Finset.filter (fun s => f2.sets s) (f2.ground.powerset)
  let SP := Finset.filter
    (fun s => ∃ (x y : Finset α), f1.sets x ∧ f2.sets y ∧ s = x ∪ y)
    ((f1.ground ∪ f2.ground).powerset)
  dsimp [SetFamily.normalized_degree_sum]
  rw [direct_Product_total_size_of_hyperedges f1 f2 disj]
  rw [direct_Product_number_of_hyperedges f1 f2 disj]
  let dpg := direct_product_ground_set_card f1 f2 disj
  rw [dpg]
  simp
  norm_cast
  ring_nf
  simp
  have :f2.number_of_hyperedges * f1.number_of_hyperedges * (↑f1.ground.card + ↑f2.ground.card)
    = f1.number_of_hyperedges * f2.number_of_hyperedges * f1.ground.card + f1.number_of_hyperedges * f2.number_of_hyperedges * f2.ground.card := by
    ring
  rw [this]
  ring_nf
