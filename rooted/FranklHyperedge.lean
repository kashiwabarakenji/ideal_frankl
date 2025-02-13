import LeanCopilot
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Finset.Union
import Mathlib.Tactic
import rooted.CommonDefinition
import rooted.RootedCircuits
import rooted.RootedImplication
import rooted.ClosureOperator
import rooted.RootedFrankl
import rooted.RootedSets

variable {α : Type}  [DecidableEq α] [Fintype α]

open Classical

--X点優位
def superior (SF:ClosureSystem α) [DecidablePred SF.sets] (X: Finset α) :Prop :=
  (SF.ground.powerset.filter (fun s => SF.sets s ∧ X ⊆ s)).card >
  (SF.ground.powerset.filter (fun s => SF.sets s ∧ X ∩ s = ∅)).card

--X abundant if normalized_Degree_sum > 0
noncomputable def normalized_degree_sum (SF:ClosureSystem α) [DecidablePred SF.sets] (X: Finset α) :ℤ :=
  ∑ s ∈ (SF.ground.powerset.filter SF.sets), 2*(X ∩ s).card - X.card * SF.number_of_hyperedges

/-使わなかった。
lemma sum_count_eq {S : Finset (Finset α)}  :
  ∑ v : α, Finset.card {A ∈ S | v ∈ A} = ∑ A ∈ S, ∑ v : α, if v ∈ A then 1 else 0 := by
  -- カード数の定義を使って書き換え
  rw [Finset.sum_comm]
  congr with A
  rw [Finset.card_eq_sum_ones, Finset.sum_boole]
  simp_all only [Finset.sum_const, smul_eq_mul, mul_one, Nat.cast_id]

lemma sum_degree_eq_sum_card (S : Finset (Finset α)) :
  ∑ v : α, Finset.card {A ∈ S | v ∈ A} = ∑ A ∈ S, Finset.card A := by
  rw [sum_count_eq]
  simp_all only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
-/

--Xに関するdouble counting lemmaも証明した方がいい？
lemma double_counting_lemma (SF:ClosureSystem α) [DecidablePred SF.sets] (X: Finset α) :
  ∑ s ∈ (SF.ground.powerset.filter SF.sets), (X ∩ s).card = ∑ v ∈ X,SF.degree v :=
by
  dsimp [SetFamily.degree]

  --hyperedge sと頂点vが、v∈ sが成り立つ個数についてsを先に和を計算するか、vの和を先に計算するかの違い。
  --上の補題を直接適用できない。s.cardでなくて、(s ∩ X).cardになっているので。
  let S := Finset.filter SF.sets SF.ground.powerset
  have : ∑ s ∈ S, (X ∩ s).card
       = ∑ s ∈ S, ∑ v ∈ X, if v ∈ s then 1 else 0 := by
    congr with s
    -- (X ∩ s).card を ∑ v in X, if v ∈ s then 1 else 0 で書き換え
    rw [Finset.card_eq_sum_ones, Finset.sum_boole]
    simp_all only [Finset.sum_const, smul_eq_mul, mul_one, Nat.cast_id]
    rfl
  -- 上記の式を使って和の順序を交換
  rw [this, Finset.sum_comm]
  -- 内側の和を書き換え: ∑ s in S, if v ∈ s then 1 else 0 = (filter (λ s, v ∈ s) S).card

  rw [Finset.sum_congr rfl]
  symm
  norm_cast

  intro x a
  simp_all only [Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_boole, Nat.cast_id, S]
  congr 1
  rw [Finset.filter_filter]

lemma sum_nonpos_exists_nonpos {α : Type} [DecidableEq α]
  (s : Finset α) (nonempty : s ≠ ∅) (f : α → ℤ) (h : s.sum f ≤ 0) :
  ∃ x ∈ s, f x ≤ 0 := by
  contrapose! h
  -- すべての x ∈ s について f x > 0 であると仮定
  have pos_sum : ∀ x ∈ s, 0 < f x := by simpa using h
  -- Finset.sum_pos を適用するための条件を確認
  have : 0 < s.sum f := Finset.sum_pos pos_sum (Finset.nonempty_of_ne_empty nonempty)
  simp_all only [ne_eq, implies_true]

lemma nds_and_rare (SF:ClosureSystem α) [DecidablePred SF.sets] (X: Finset α) (nonemp: X.Nonempty):
  normalized_degree_sum SF X <= 0 → ∃ v: α, v ∈ X ∧ SF.is_rare v :=
by
  dsimp [normalized_degree_sum]
  dsimp [SetFamily.number_of_hyperedges] --展開しなくてもいいかも。
  intro h
  --dsimp [is_rare]
  simp at h
  have :∑ x ∈ Finset.filter SF.sets SF.ground.powerset, 2 * ↑(X ∩ x).card = 2 * ∑ x ∈ Finset.filter SF.sets SF.ground.powerset, ↑(X ∩ x).card :=
  by
    rw [Finset.mul_sum]
  have hh: 2 * ∑ x ∈ Finset.filter SF.sets SF.ground.powerset, ↑(X ∩ x).card
    ≤ ↑X.card * ↑(Finset.filter (fun s => SF.sets s) SF.ground.powerset).card :=
  by
    rw [← this]
    simp_all only
    simp_rw [← this]
    simp_all only
    linarith

  have := double_counting_lemma SF X
  norm_cast at hh
  norm_cast at this
  have :2 * ∑ v ∈ X, SF.degree v ≤  X.card * (Finset.filter (fun s => SF.sets s) SF.ground.powerset).card :=
  by
    simp_all only [Nat.cast_sum]
    rw [← this]
    simp_all only
    rw [← this]
    simp_all only
    linarith
  have :∃ v ∈ X, 2*SF.degree v - ↑(Finset.filter (fun s => SF.sets s) SF.ground.powerset).card ≤ 0 :=
  by
    apply sum_nonpos_exists_nonpos X
    · intro a
      subst a
      simp_all only [Finset.not_nonempty_empty]
    · simp
      convert this
      simp_all only [Nat.cast_sum]
      ring_nf
      rw [Finset.sum_mul]

  obtain ⟨v,hv⟩ := this
  use v
  constructor
  · simp_all only [Nat.cast_sum, tsub_le_iff_right, zero_add]
  · dsimp [SetFamily.is_rare]
    dsimp [SetFamily.number_of_hyperedges]
    exact hv.2

--同じ定理を前のidealのリポジトリでも証明。でもここで必要だったのは、cardじゃなくて和だったかも。
--filter_sum_funcがdisjointの和を計算しているので似ている。
lemma card_filter_add_card_filter_compl {α : Type*} (S : Finset α) (P Q : α → Prop)
  [DecidablePred P] [DecidablePred Q] :
  (Finset.filter (λ s=> P s) S).card =
    (Finset.filter (λ s => P s ∧ Q s) S).card +
    (Finset.filter (λ s => P s ∧ ¬ Q s) S).card :=
by
  -- まず、`S.filter (λ x => P x)` を集合 `T` と呼ぶことにする
  let T := S.filter (λ x => P x)
  -- `T` の中でさらに `Q x` を満たす・満たさないに分割
  calc
    T.card
    = (T.filter Q).card + (T.filter (λ x => ¬ Q x)).card
      -- ここで `Finset.filter_card_add_filter_neg_card_eq_card` を `T` と `p = Q` に適用
      := by
       let ff := @Finset.filter_card_add_filter_neg_card_eq_card _ T Q
       simp_all [T]
    -- あとは `T.filter Q = S.filter (λ x => P x ∧ Q x)` に書き換えればよい
  _ = (S.filter (λ x => P x ∧ Q x)).card + (S.filter (λ x => P x ∧ ¬ Q x)).card
      := by
        rw [Finset.filter_filter, Finset.filter_filter]  -- P と Q を合わせただけ

lemma sum_filter_add_sum_filter_compl {α : Type*} (S : Finset α) (P Q : α → Prop) (f:α → ℤ)
  [DecidablePred P] [DecidablePred Q] :
  ∑ s ∈ (Finset.filter (λ s=> P s) S),f s =
    ∑ s ∈ (Finset.filter (λ s => P s ∧ Q s) S),f s +
    ∑ s∈ (Finset.filter (λ s => P s ∧ ¬ Q s) S), f s :=
by
  let T := S.filter (λ x => P x)
  have : ∑ s ∈ T, f s
  = ∑ s ∈ (T.filter Q), f s + ∑ s ∈ (T.filter (λ x => ¬ Q x)),f s :=
   by
     let fs := Finset.sum_filter_add_sum_filter_not T Q f
     simp_all [T]
  dsimp [T] at this
  simp at this
  rw [this]
  rw [Finset.filter_filter]
  simp
  rw [Finset.filter_filter]

lemma two_superior_implies_nds_positive (SF: ClosureSystem α) [DecidablePred SF.sets] (x y :SF.ground) (neq: x ≠ y):
  superior SF ({x.val,y.val}:Finset α) → normalized_degree_sum SF ({x.val,y.val}:Finset α) > 0 :=
by

  dsimp [superior]
  dsimp [normalized_degree_sum]
  intro h
  have :({x.val, y.val}:Finset α).card = 2:=
  by
    simp_all only [ne_eq, gt_iff_lt]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    simp_all only [Subtype.mk.injEq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
      Finset.card_singleton, Nat.reduceAdd]

  rw [this]
  simp
  --2を和の外に出して、2で割るだけでこんなに変形するのはおかしいかも。
  suffices SF.number_of_hyperedges < ∑ x_1 ∈ Finset.filter SF.sets SF.ground.powerset, (({x.val, y.val} ∩ x_1).card : ℤ) from
  by
    have : 2* ∑ x_1 ∈ Finset.filter SF.sets SF.ground.powerset, ↑({x.val, y.val} ∩ x_1).card =
    ∑ x_1 ∈ Finset.filter SF.sets SF.ground.powerset, 2 * ↑({x.val, y.val} ∩ x_1).card :=
    by
      simp_all only [ne_eq, gt_iff_lt]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      simp_all only [Subtype.mk.injEq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,Finset.card_singleton, Nat.reduceAdd]
      symm
      simp_rw [Finset.mul_sum]
    simp_all only [ne_eq, gt_iff_lt]
    have :2 * SF.number_of_hyperedges < 2 * ∑ x_1 ∈ Finset.filter SF.sets SF.ground.powerset, ({↑x, ↑y} ∩ x_1).card :=
    by
      simp_all only [Nat.cast_sum, Nat.ofNat_pos, mul_lt_mul_left]
    simp_all only [Nat.cast_sum, Nat.ofNat_pos, mul_lt_mul_left, gt_iff_lt]
    --obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    simp_all only [Subtype.mk.injEq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd]
    linarith

  --sが{x,y}とちょうど1交わるか、そうでないかで、ゴールの条件を分割。
  let P : Finset α → Prop := (fun s => SF.sets s)
  let Q : Finset α → Prop := (fun s => ({x.val,y.val}∩s).card = 1)

  have notone: ∑ s ∈ SF.ground.powerset.filter (fun s => P s), ↑({x.val, y.val} ∩ s).card = ∑ s ∈ (SF.ground.powerset.filter (fun s => (P s) ∧ (Q s))), ↑({x.val, y.val} ∩ s).card + ∑ s ∈ (SF.ground.powerset.filter (fun s => (P s ∧ ¬ (Q s)))), ↑({x.val, y.val} ∩ s).card :=
  by
    let sf := sum_filter_add_sum_filter_compl SF.ground.powerset P Q (fun s => ({x.val,y.val}∩ s).card)
    simp at sf
    norm_cast
    norm_cast at sf

  have notone2: ∑ ss ∈ (SF.ground.powerset.filter (fun s => (P s ∧ ¬ (Q s)))), ({x.val, y.val} ∩ ss).card = ∑ ss ∈ (SF.ground.powerset.filter (fun s => SF.sets s ∧ {x.val, y.val} ⊆ s)), ({x.val, y.val} ∩ ss).card + ∑ ss ∈  (SF.ground.powerset.filter (fun s => SF.sets s ∧ {x.val, y.val} ∩ s = ∅)), ({x.val, y.val} ∩ ss).card :=
  by
    have pq_rule: ∀ s : Finset α, (P s ∧ ¬ (Q s)) ↔  SF.sets s ∧ ({x.val, y.val} ⊆ s ∨ {x.val, y.val} ∩ s = ∅) :=
    by
      dsimp [P]
      dsimp [Q]
      intro s

      have eq2: ({x.val, y.val}:Finset α).card = 2 :=
      by
        simp_all only [ge_iff_le, Q, P]

      apply Iff.intro
      · intro hh
        constructor
        · simp_all only [ne_eq, gt_iff_lt, Q, P]

        by_cases emp:({↑x, ↑y} ∩ s).card = 0
        case pos =>
          right
          simp_all only [ne_eq, gt_iff_lt, zero_ne_one, not_false_eq_true, and_true, Finset.card_eq_zero, Q, P]
        case neg =>
          left
          simp_all only [ne_eq, gt_iff_lt, Finset.card_eq_zero, Q, P]
          have geq2: ({↑x, ↑y} ∩ s).card ≥ 2 :=
          by
            contrapose emp

            simp at emp
            have :({↑x, ↑y} ∩ s).card = 0 ∨ ({↑x, ↑y} ∩ s).card = 1:=
            by
              rw [Nat.lt_succ_iff] at emp
              rw [Nat.le_add_one_iff] at emp
              simp_all only [nonpos_iff_eq_zero, Finset.card_eq_zero, zero_add, or_false, Finset.card_empty,
                zero_ne_one, Q, P]
            simp_all only [Finset.card_eq_zero, or_false, not_true_eq_false, not_false_eq_true, Q, P]

          have : ( {↑x, ↑y} ∩ s ).card ≤ ({x.val, y.val}:Finset α).card :=
          by
            have : ( ({x.val, y.val}:Finset α) ∩ s ) ⊆ ({x.val, y.val}:Finset α) :=
            by
              simp_all only [ge_iff_le, Finset.inter_subset_left, Q, P]
            apply Finset.card_le_card this

          rw [eq2] at this

          have h := Nat.eq_iff_le_and_ge.mpr ⟨this, geq2⟩

          --#check @Finset.inter_subset_right _ _ ({x.val, y.val}:Finset α) s
          let fe := (Finset.eq_of_subset_of_card_le (@Finset.inter_subset_left _ _ ({x.val, y.val}:Finset α) s))

          have : ({x.val, y.val}:Finset α).card ≤ ({x.val, y.val} ∩ s).card :=
          by
            rw [eq2]
            exact geq2

          specialize fe this

          simp_all only [OfNat.ofNat_ne_one, not_false_eq_true, and_true, Finset.insert_ne_empty, ge_iff_le, le_refl,
            Finset.inter_eq_left, Q, P]

      · intro h
        constructor
        · simp_all only [ne_eq, gt_iff_lt, Q, P]
        · cases h.2 with
          | inl h_2 =>
            have : {↑x, ↑y} ∩ s = {↑x, ↑y} :=
            by
              simp_all only [ne_eq, gt_iff_lt, true_or, and_true, Finset.inter_eq_left, Q, P]
            rw [this]
            rw [eq2]
            trivial

          | inr h_3 =>
            rw [h_3]
            simp_all only [ne_eq, gt_iff_lt, or_true, and_true, Finset.card_empty, zero_ne_one, not_false_eq_true, Q, P]
    haveI : DecidablePred (λ s => P s ∧ ¬ Q s) := inferInstance
    --rw [Finset.sum_congr rfl]

    -- pq_rule : ∀ (s : Finset α), P s ∧ ¬Q s ↔ SF.sets s ∧ ({↑x, ↑y} ⊆ s ∨ {↑x, ↑y} ∩ s = ∅)
    --pq_ruleを使って、ゴールのfilterの中身を書き換えたいけど、いまいちfilter_congrがうまくいかない。
    have pq_rule2:Finset.filter (fun s => P s ∧ ¬Q s) SF.ground.powerset = Finset.filter (fun s => SF.sets s ∧ ({↑x, ↑y} ⊆ s ∨ {↑x, ↑y} ∩ s = ∅)) SF.ground.powerset :=
    by
      --haveI : DecidablePred (λ s => P s ∧ ¬ Q s) := inferInstance
      ext x
      apply Iff.intro
      · rename_i x_1 this_1 this_2
        intro a
        simp_all [Q, P]
        --obtain ⟨val, property⟩ := x_1
        obtain ⟨val_1, property_1⟩ := y
        obtain ⟨left, right⟩ := a
        obtain ⟨left_1, right⟩ := right
        simp_all only [Subtype.mk.injEq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
          Finset.card_singleton, Nat.reduceAdd, P]
      ·
        intro a
        simp_all only [ne_eq, gt_iff_lt, and_congr_right_iff, Finset.mem_filter, Finset.mem_powerset, and_self, Q, P]

    have pq_rule3: Finset.filter (fun s => SF.sets s ∧ ({↑x, ↑y} ⊆ s ∨ {↑x, ↑y} ∩ s = ∅)) SF.ground.powerset = Finset.filter (fun s => SF.sets s ∧ {↑x, ↑y} ⊆ s) SF.ground.powerset ∪ Finset.filter (fun s => SF.sets s ∧ {↑x, ↑y} ∩ s = ∅) SF.ground.powerset :=
    by
      ext x
      apply Iff.intro
      ·
        intro a
        simp_all only [ne_eq, gt_iff_lt, and_congr_right_iff, Finset.mem_filter, Finset.mem_powerset, Finset.mem_union,
          true_and, Q, P]
      ·
        rename_i x_1 this_1 this_2
        intro a
        simp_all [Q, P]
        obtain ⟨val, property⟩ := this_1
        obtain ⟨val_1, property_1⟩ := y
        simp_all only [Subtype.mk.injEq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
          Finset.card_singleton, Nat.reduceAdd, P]
        cases a with
        | inl h_1 => simp_all only [true_or, and_self, P]
        | inr h_2 => simp_all only [or_true, and_self, P]

    let R2: Finset α → Prop:= (fun s => (({x.val, y.val}:Finset α) ⊆ s))
    let R0: Finset α → Prop:= (fun s => (({x.val, y.val}:Finset α) ∩ s = ∅))
    let f: Finset α → Nat := fun s => (({x.val, y.val}:Finset α) ∩ s).card
    --set hand := (∑ ss ∈ Finset.filter (fun ss => SF.sets ss ∧ ((R2 ss) ∨ (R0 ss))) SF.ground.powerset, f ss) with hand_def

    have hand_this:(∑ s ∈ Finset.filter (fun s => SF.sets s ∧ ((R2 s) ∨ (R0 s))) SF.ground.powerset, f s) =
       ∑ s ∈ (Finset.filter (fun s => SF.sets s ∧ (R2 s)) SF.ground.powerset ∪ (Finset.filter (fun s => SF.sets s ∧ (R0 s)) SF.ground.powerset)), f s:=

    by
      --rw [←hand]
      --rw [hand]
      --dsimp [hand]
      rw [pq_rule3]

    /-
    have : ∑ s ∈ Finset.filter (fun s => SF.sets s ∧ ({↑x, ↑y} ⊆ s ∨ {↑x, ↑y} ∩ s = ∅)) SF.ground.powerset, ({↑x, ↑y} ∩ s).card =
      ∑ s ∈ Finset.filter (fun s => SF.sets s ∧ ({↑x, ↑y} ⊆ s ∨ {↑x, ↑y} ∩ s = ∅)) SF.ground.powerset, ({↑x, ↑y} ∩ s).card  :=
      rfl
    -/
    have tt: (∑ s ∈ Finset.filter (fun s => SF.sets s ∧ ((R2 s) ∨ (R0 s))) SF.ground.powerset, f s) =
        (∑ s ∈ Finset.filter (fun s => SF.sets s ∧ (R2 s)) SF.ground.powerset, f s) +
       (∑ s ∈ Finset.filter (fun s => SF.sets s ∧ (R0 s)) SF.ground.powerset, f s) :=
    by

      suffices ∑ s ∈ (Finset.filter (fun s => SF.sets s ∧ (R2 s)) SF.ground.powerset ∪ (Finset.filter (fun s => SF.sets s ∧ (R0 s)) SF.ground.powerset)), f s = (∑ s ∈ Finset.filter (fun s => SF.sets s ∧ (R2 s)) SF.ground.powerset, f s) +
       (∑ s ∈ Finset.filter (fun s => SF.sets s ∧ (R0 s)) SF.ground.powerset, f s) from
        by
          simp_all only [ne_eq, gt_iff_lt, and_congr_right_iff, Q, P, R2, R0, f]

      rw [Finset.sum_union]
      dsimp [Disjoint]
      intro s hs hhs
      by_contra h_contra
      simp at h_contra
      rw [← @Finset.not_nonempty_iff_eq_empty] at h_contra
      rw [Mathlib.Tactic.PushNeg.not_not_eq] at h_contra
      obtain ⟨xx,hx⟩ := h_contra
      let hs := hs hx
      let hhs := hhs hx
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_filter] at hhs
      rw [@and_rotate] at hs
      rw [@and_rotate] at hhs
      dsimp [R2] at hs
      dsimp [R0] at hhs
      let hs0 := hs.2.1
      let hhs0 := hhs.2.1
      rw [Finset.subset_iff] at hs0
      rw [←Finset.disjoint_iff_inter_eq_empty] at hhs0
      simp_all only [ne_eq, gt_iff_lt, and_congr_right_iff, and_true, true_and, Finset.mem_insert, Finset.mem_singleton,
        true_or, Finset.insert_inter_of_mem, or_true, Finset.singleton_inter_of_mem, Finset.insert_ne_empty,
        Finset.mem_powerset, false_and, and_false, Q, f, R0, R2, P]

    show ∑ ss ∈ @Finset.filter (Finset α) (fun s => P s ∧ ¬Q s) (fun a => instDecidableAnd) SF.ground.powerset, ({↑x, ↑y} ∩ ss).card =
      ∑ ss ∈ Finset.filter (fun s => SF.sets s ∧ {↑x, ↑y} ⊆ s) SF.ground.powerset, ({↑x, ↑y} ∩ ss).card +
      ∑ ss ∈ Finset.filter (fun s => SF.sets s ∧ {↑x, ↑y} ∩ s = ∅) SF.ground.powerset, ({↑x, ↑y} ∩ ss).card
    rw [Finset.filter_congr_decidable]
    simp [pq_rule2]
    simp_all only [ne_eq, gt_iff_lt, and_congr_right_iff, Q, f, R0, R2, P]

  show SF.number_of_hyperedges < ∑ x_1 ∈ Finset.filter SF.sets SF.ground.powerset, (({x.val, y.val} ∩ x_1).card : ℤ)

  -- cardが1の部分とcardが0 or 2の部分で分けて考える。
  --1の部分は、常に0になる。
  --0 or 2の部分は正になる。
  --それぞれ補題にする。

  dsimp [SetFamily.number_of_hyperedges]

  --イコール1の部分は等号がなりたつ。
  have :∑ x_1 ∈ Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card = 1) SF.ground.powerset, ↑({x.val, y.val} ∩ x_1).card = (Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card = 1) SF.ground.powerset).card :=
  by
    let f :Finset α → ℕ := fun s => ({x.val, y.val} ∩ s).card
    let S := Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card = 1) SF.ground.powerset
    --let fs := Finset.sum (Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card = 1) SF.ground.powerset) (λ _ => 1)
    calc
      ∑ x_1 ∈ Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card = 1) SF.ground.powerset, ↑({x.val, y.val} ∩ x_1).card
      = ∑ x_1 ∈ S, f x_1 :=
      by
        simp_all only [ne_eq, gt_iff_lt, Q, P, S, f]
    _ = ∑ x ∈ S, 1 := by
        apply Finset.sum_congr rfl
        intros x hx
        simp_all only [ne_eq, gt_iff_lt, Finset.mem_filter, Finset.mem_powerset, Q, P, S, f]
    _ = S.card := by simp_all only [ne_eq, gt_iff_lt, Finset.sum_const, smul_eq_mul, mul_one, f, Q, P, S]
    _ = (Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card = 1) SF.ground.powerset).card := by simp_all only [ne_eq, gt_iff_lt, f, Q, P, S]

  --以下の式から成り立つ。
  have : ↑(Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card ≠ 1) SF.ground.powerset).card <
  ∑ x_1 ∈ Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card ≠ 1) SF.ground.powerset, ↑({x.val, y.val} ∩ x_1).card :=
  by
    --イコール0の部分とイコール2の部分に分解する必要がある。
    sorry











































--sum_filter_add_sum_filter_complを使って分解。

  --補題の設定
  -- sと{x,y}の関係は、
  --{x,y}を含むか、disjointか、片方のみと交わるか。
  --片方のみと交わる場合は、
