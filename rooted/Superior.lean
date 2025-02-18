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
import rooted.ClosureOperator
import rooted.RootedSets
import rooted.RootedCircuits
import rooted.RootedImplication
import rooted.RootedFrankl


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

--two_superior_implies_nds_positiveの証明が長いので、一部を補題として分離。
lemma two_superior_implies_notone_positive (SF: ClosureSystem α) [DecidablePred SF.sets] (x y :SF.ground) (neq: x ≠ y):
  superior SF ({x.val,y.val}:Finset α) →
  (Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card ≠ 1) SF.ground.powerset).card <
  ∑ x_1 ∈ Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card ≠ 1) SF.ground.powerset, (({x.val, y.val} ∩ x_1).card:Int)  :=
by
  let P : Finset α → Prop := (fun s => SF.sets s)
  let Q : Finset α → Prop := (fun s => ({x.val,y.val}∩s).card = 1)

  --次の補題hand_thisのための補題
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
      obtain ⟨val_1, property_1⟩ := y
      simp_all only [Subtype.mk.injEq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
        Finset.card_singleton, Nat.reduceAdd, P]
      cases a with
      | inl h_1 => simp_all only [true_or, and_self, P]
      | inr h_2 => simp_all only [or_true, and_self, P]

  let R2: Finset α → Prop:= (fun s => (({x.val, y.val}:Finset α) ⊆ s))
  let R0: Finset α → Prop:= (fun s => (({x.val, y.val}:Finset α) ∩ s = ∅))
  let f: Finset α → Int := fun s => ((({x.val, y.val}:Finset α) ∩ s).card:Int)

  --証明はpq_ruleの中に片側がある。
  have eq2: ({x.val, y.val}:Finset α).card = 2 :=
      by
        simp_all only [ne_eq, Q, P]
        obtain ⟨val, property⟩ := x
        obtain ⟨val_1, property_1⟩ := y
        simp_all only [Subtype.mk.injEq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
          Finset.card_singleton, Nat.reduceAdd, P]

  have sub_eq_2:∀ s:Finset α, {x.val,y.val} ⊆ s ↔ ({x.val, y.val} ∩ s).card = 2 :=
  by
    intro s
    apply Iff.intro
    · intro h
      have : {↑x, ↑y} ∩ s = {↑x, ↑y} :=
      by
        simp_all only [ne_eq, Finset.inter_eq_left]
      have geq2: ({↑x, ↑y} ∩ s).card >= 2 :=
      by
        rw [this]
        simp_all only [ne_eq, Finset.inter_eq_left, ge_iff_le, le_refl]

      have : ( {↑x, ↑y} ∩ s ).card ≤ ({x.val, y.val}:Finset α).card :=
      by
        have : ( ({x.val, y.val}:Finset α) ∩ s ) ⊆ ({x.val, y.val}:Finset α) :=
        by
          simp_all only [ne_eq, Finset.inter_eq_left, ge_iff_le, Finset.inter_subset_left]
        apply Finset.card_le_card this

      rw [eq2] at this

      simp_all only [ne_eq, Finset.inter_eq_left, ge_iff_le]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      simp_all only [Subtype.mk.injEq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
        Finset.card_singleton, Nat.reduceAdd]
      omega

    · intro h
      have :({x.val, y.val}:Finset α) ∩ s = {x.val, y.val} :=
      by
        have h_subset : {x.val, y.val} ∩ s ⊆ {x.val, y.val} :=
        by
          simp_all only [ne_eq, Finset.inter_subset_left]
        have h_card : ({↑x, ↑y}:Finset α).card = ({↑x, ↑y} ∩ s).card :=
        by
          simp_all only [ne_eq, Finset.inter_subset_left]
        exact Finset.eq_of_subset_of_card_le h_subset (le_of_eq h_card)
      simp_all only [ne_eq, Finset.inter_eq_left]

  --notone_cardの証明に使っている。
  have hand_this:(∑ s ∈ Finset.filter (fun s => SF.sets s ∧ ((R2 s) ∨ (R0 s))) SF.ground.powerset, f s) =
       ∑ s ∈ (Finset.filter (fun s => SF.sets s ∧ (R2 s)) SF.ground.powerset ∪ (Finset.filter (fun s => SF.sets s ∧ (R0 s)) SF.ground.powerset)), f s:=
    by
      rw [pq_rule3]

  --set hand := (∑ ss ∈ Finset.filter (fun ss => SF.sets ss ∧ ((R2 ss) ∨ (R0 ss))) SF.ground.powerset, f ss) with hand_def
  --1でない場合の和のほうの分解。コメントアウトすると、なぜかnotone_cardの証明でエラー。
  have notone_sum: (∑ s ∈ Finset.filter (fun s => SF.sets s ∧ ((R2 s) ∨ (R0 s))) SF.ground.powerset, f s) =
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
    --このあたりは、sumとcardで共通なので、補題にしてもよい。
    dsimp [R2] at hs
    dsimp [R0] at hhs
    let hs0 := hs.2.1
    let hhs0 := hhs.2.1
    rw [Finset.subset_iff] at hs0
    rw [←Finset.disjoint_iff_inter_eq_empty] at hhs0
    simp_all only [ne_eq, gt_iff_lt, and_congr_right_iff, and_true, true_and, Finset.mem_insert, Finset.mem_singleton,
      true_or, Finset.insert_inter_of_mem, or_true, Finset.singleton_inter_of_mem, Finset.insert_ne_empty,
      Finset.mem_powerset, false_and, and_false, Q, f, R0, R2, P]

  --コメントアウトすると、not1_into_0or2の証明やnotone_cardの証明でエラー。
  have pq_rule: ∀ s : Finset α, (P s ∧ ¬ (Q s)) ↔  SF.sets s ∧ (R2 s ∨ R0 s) :=
    by
      dsimp [P]
      dsimp [Q]
      dsimp [R0,R2]
      intro s

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

    --pq_ruleの証明がおわり

  --notoneのsumのほうの分解。notone_sumを利用している。
  have notone_sum2: ∑ ss ∈ (SF.ground.powerset.filter (fun s => (P s ∧ ¬ (Q s)))), f ss =
  ∑ ss ∈ (SF.ground.powerset.filter (fun s => P s ∧ R2 s)), f ss + ∑ ss ∈ (SF.ground.powerset.filter (fun s => P s ∧ R0 s)), f ss :=
  by
    haveI : DecidablePred (λ s => P s ∧ ¬ Q s) := inferInstance  --ないとエラー。

    rw [Finset.filter_congr_decidable]

    simp_all only [R2, Q, f, P, R0]


  --/- 今の構成では利用してないよう。使う時に復活させる。
  have not1_into_0or2: Finset.filter (fun s => P s ∧ ¬Q s) SF.ground.powerset = Finset.filter (fun s => SF.sets s ∧ (R2 s ∨ R0 s)) SF.ground.powerset :=
    by
      --haveI : DecidablePred (λ s => P s ∧ ¬ Q s) := inferInstance
      ext x
      apply Iff.intro
      ·
        intro a
        simp_all [Q, P]
        obtain ⟨val_1, property_1⟩ := y
        obtain ⟨left, right⟩ := a
        obtain ⟨left_1, right⟩ := right
        simp_all only [Subtype.mk.injEq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
          Finset.card_singleton, Nat.reduceAdd, P]
      · intro a
        dsimp [R0,R2]
        simp_all only [ne_eq, gt_iff_lt, and_congr_right_iff, Finset.mem_filter, Finset.mem_powerset, and_self, Q, P]

  have disjoint_0and2: Finset.filter (fun s => P s ∧ R2 s) SF.ground.powerset ∩ (Finset.filter (fun s => P s ∧ R0 s)) SF.ground.powerset = ∅ :=
  by
    have :∀ s :Finset α, ¬ (R0 s ∧ R2 s ) :=
      by
        intro h hh
        dsimp [R2,R0] at hh
        rw [Finset.subset_iff] at hh
        rw [←Finset.disjoint_iff_inter_eq_empty] at hh
        simp_all only [ne_eq, and_congr_right_iff, Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
          Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, R2, Q, f, P, R0]
        obtain ⟨left, right⟩ := hh
        simp_all only [Subtype.mk.injEq, not_true_eq_false, P]

    ext s
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · intro h
      simp_all only [ne_eq, and_congr_right_iff, not_and, Finset.mem_powerset, Finset.not_mem_empty, R2, Q, f, P, R0]
      obtain ⟨left, right⟩ := h
      simp_all only [Subtype.mk.injEq, P]
      simp_all only [not_true_eq_false, imp_false, Finset.card_empty, OfNat.zero_ne_ofNat, and_false, f, P, R2, Q, R0]
    · intro h
      simp_all only [ne_eq, and_congr_right_iff, not_and, Finset.not_mem_empty, R2, Q, f, P, R0]

  have notone_card: (SF.ground.powerset.filter (fun s => (P s ∧ ¬ (Q s)))).card =
  (SF.ground.powerset.filter (fun s => P s ∧ R2 s)).card + (SF.ground.powerset.filter (fun s => P s ∧ R0 s)).card :=
  by
    rw [not1_into_0or2]
    rw [pq_rule3]
    rw [Finset.card_union]
    simp_all only [ne_eq, and_congr_right_iff, Finset.card_empty, tsub_zero, R2, Q, f, P, R0]

  intro sp
  show (Finset.filter (fun s => SF.sets s ∧ ({↑x, ↑y} ∩ s).card ≠ 1) SF.ground.powerset).card <
  ∑ x_1 ∈ Finset.filter (fun s => SF.sets s ∧ ({↑x, ↑y} ∩ s).card ≠ 1) SF.ground.powerset, f x_1

  suffices (Finset.filter (fun s => P s ∧ ¬Q s) SF.ground.powerset).card <
  ∑ x_1 ∈(Finset.filter (fun s => P s ∧ ¬Q s) SF.ground.powerset), f x_1 from
  by
    dsimp [P] at this
    dsimp [Q] at this
    dsimp [f] at this
    --convert this
    simp_all only [ne_eq, and_congr_right_iff, Nat.cast_add, f, P, R2, Q, R0]

  rw [notone_card]
  rw [notone_sum2]
  show (Finset.filter (fun s => P s ∧ R2 s) SF.ground.powerset).card +
    (Finset.filter (fun s => P s ∧ R0 s) SF.ground.powerset).card <
  ∑ ss ∈ Finset.filter (fun s => P s ∧ R2 s) SF.ground.powerset, f ss +
    ∑ ss ∈ Finset.filter (fun s => P s ∧ R0 s) SF.ground.powerset, f ss

  dsimp [superior] at sp
  have sp2:(Finset.filter (fun s => P s ∧ R2 s) SF.ground.powerset).card >
  (Finset.filter (fun s => P s ∧ R0 s) SF.ground.powerset).card :=
  by
    simp_all only [ne_eq, and_congr_right_iff, gt_iff_lt, R2, Q, f, P, R0]

  --うまくいかないので、f-1を持ち出すのは良い方針ではないのかも。
  --suffices  ∑ ss ∈ Finset.filter (fun s => P s ∧ R2 s) SF.ground.powerset, (f - 1) ss +
  --  ∑ ss ∈ Finset.filter (fun s => P s ∧ R0 s) SF.ground.powerset, (f - 1) ss > 0 from

  have F2lem : ∑ ss ∈ Finset.filter (fun s => P s ∧ R2 s) SF.ground.powerset, f ss = ∑ ss ∈ (Finset.filter (fun s => P s ∧ ({x.val,y.val} ∩ s).card = 2) SF.ground.powerset), f ss :=
  by
    simp_all only [ne_eq, and_congr_right_iff, gt_iff_lt, f, P, R2, Q, R0]

  have F2lem2 : (Finset.filter (fun s => P s ∧ R2 s) SF.ground.powerset).card = (Finset.filter (fun s => P s ∧ ({x.val,y.val} ∩ s).card = 2) SF.ground.powerset).card :=
  by
    simp_all only [ne_eq, and_congr_right_iff, gt_iff_lt, f, P, R2, Q, R0]

  have F2: ∑ ss ∈ Finset.filter (fun s => P s ∧ R2 s) SF.ground.powerset, f ss = 2*(Finset.filter (fun s => P s ∧ R2 s) SF.ground.powerset).card :=
  by
    dsimp [R2]
    dsimp [f]
    rw [F2lem]
    dsimp [f]
    rw [F2lem2]
    rw [Finset.card_eq_sum_ones]
    let filtered_sets := Finset.filter (fun s => P s ∧ ({↑x, ↑y} ∩ s).card = 2) SF.ground.powerset
    have h1 : ∀ s ∈ filtered_sets, ({↑x, ↑y} ∩ s).card = 2 :=
    by
      intro s hs
      simp at hs
      dsimp [filtered_sets] at hs
      rw [Finset.mem_filter] at hs
      exact hs.2.2

    have h2 : ∑ ss ∈ filtered_sets, ↑(({x.val, y.val}:Finset α) ∩ ss).card = ∑ ss ∈ filtered_sets, 2 :=
    by
      apply Finset.sum_congr rfl
      intro s hs
      rw [h1 s hs]

    rw [Finset.sum_const]

    have h3 : filtered_sets.card = ∑ x ∈ filtered_sets, 1 :=
    by
      rw [Finset.card_eq_sum_ones]

    rw [h3]
    simp
    ring_nf
    dsimp [filtered_sets] at h2
    norm_cast
    rw [h2]

    dsimp [filtered_sets]
    rw [Finset.sum_const]
    rfl

  have F0: ∑ ss ∈ Finset.filter (fun s => P s ∧ R0 s) SF.ground.powerset, f ss = 0 :=
  by
    dsimp [R0]
    dsimp [f]
    apply Finset.sum_eq_zero
    intros ss hss
    rw [Finset.mem_filter] at hss
    simp_all only [ne_eq, and_congr_right_iff, gt_iff_lt, Finset.mem_powerset, Finset.card_empty, CharP.cast_eq_zero, f,
      P, R2, Q, R0]

  simp

  suffices (Finset.filter (fun s => P s ∧ R2 s) SF.ground.powerset).card > ((Finset.filter (fun s => P s ∧ R0 s) SF.ground.powerset).card:ℤ) from
  by
    linarith

  suffices (Finset.filter (fun s => P s ∧ R2 s) SF.ground.powerset).card >
    (Finset.filter (fun s => P s ∧ R0 s) SF.ground.powerset).card from
  by
    norm_cast

  simp_all only [ne_eq, and_congr_right_iff, gt_iff_lt, Pi.sub_apply, Pi.one_apply, Nat.cast_sum, R2, Q, f, P, R0]

--イコール1の部分は等号がなりたつ。
lemma equal_one_implies_zero (SF: ClosureSystem α) [DecidablePred SF.sets] (x y :SF.ground) :

  ∑ x_1 ∈ Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card = 1) SF.ground.powerset, ↑({x.val, y.val} ∩ x_1).card = (Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card = 1) SF.ground.powerset).card :=
by
  let f :Finset α → ℕ := fun s => ({x.val, y.val} ∩ s).card
  let S := Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card = 1) SF.ground.powerset
  --let fs := Finset.sum (Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card = 1) SF.ground.powerset) (λ _ => 1)
  calc
    ∑ x_1 ∈ Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card = 1) SF.ground.powerset, ↑({x.val, y.val} ∩ x_1).card
    = ∑ x_1 ∈ S, f x_1 :=
    by
      simp_all only [ne_eq, gt_iff_lt, S, f]
  _ = ∑ x ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intros x hx
      simp_all only [ne_eq, gt_iff_lt, Finset.mem_filter, Finset.mem_powerset,  S, f]
  _ = S.card := by simp_all only [ne_eq, gt_iff_lt, Finset.sum_const, smul_eq_mul, mul_one, f, S]
  _ = (Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card = 1) SF.ground.powerset).card := by simp_all only [ne_eq, gt_iff_lt, f, S]

--2点優位であれば、2点平均abundnatという定理。
--pairのnorm_degree_sumとsuperiorのndsの関係を証明した方が良いかも。
--今の定理の証明を残したまま、新たな補題を証明する方向で改善をはかる。
theorem two_superior_implies_nds_positive (SF: ClosureSystem α) [DecidablePred SF.sets] (x y :SF.ground) (neq: x ≠ y):
  superior SF ({x.val,y.val}:Finset α) → normalized_degree_sum SF ({x.val,y.val}:Finset α) > 0 :=
by

  dsimp [superior]
  dsimp [normalized_degree_sum]
  intro sp
  have :({x.val, y.val}:Finset α).card = 2:=
  by
    simp_all only [ne_eq, gt_iff_lt]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    simp_all only [Subtype.mk.injEq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
      Finset.card_singleton, Nat.reduceAdd]

  rw [this]
  simp

  suffices SF.number_of_hyperedges < ∑ x_1 ∈ Finset.filter SF.sets SF.ground.powerset, (({x.val, y.val} ∩ x_1).card : ℤ) from
  by
    have : 2* ∑ x_1 ∈ Finset.filter SF.sets SF.ground.powerset, ↑({x.val, y.val} ∩ x_1).card =
    ∑ x_1 ∈ Finset.filter SF.sets SF.ground.powerset, 2 * ↑({x.val, y.val} ∩ x_1).card :=
    by
      simp_rw [Finset.mul_sum]
    have :2 * SF.number_of_hyperedges < 2 * ∑ x_1 ∈ Finset.filter SF.sets SF.ground.powerset, ({↑x, ↑y} ∩ x_1).card :=
    by
      simp_all only [Nat.cast_sum, Nat.ofNat_pos, mul_lt_mul_left]
    obtain ⟨val_1, property_1⟩ := y
    linarith

  --sが{x,y}とちょうど1交わるか、そうでないかで、ゴールの条件を分割。
  let P : Finset α → Prop := (fun s => SF.sets s)
  let Q : Finset α → Prop := (fun s => ({x.val,y.val}∩s).card = 1)

  have notone_sum: ∑ s ∈ SF.ground.powerset.filter (fun s => P s), ↑({x.val, y.val} ∩ s).card = ∑ s ∈ (SF.ground.powerset.filter (fun s => (P s) ∧ (Q s))), ↑({x.val, y.val} ∩ s).card + ∑ s ∈ (SF.ground.powerset.filter (fun s => (P s ∧ ¬ (Q s)))), ↑({x.val, y.val} ∩ s).card :=
  by
    let sf := sum_filter_add_sum_filter_compl SF.ground.powerset P Q (fun s => ({x.val,y.val}∩ s).card)
    simp at sf
    --norm_cast
    norm_cast at sf

    --イコール0の部分とイコール2の部分に分解する必要がある。
  have separate_card: SF.number_of_hyperedges = (Finset.filter (fun s => (P s ∧ Q s)) SF.ground.powerset).card + (Finset.filter (fun s => (P s ∧ ¬Q s)) SF.ground.powerset).card :=
  by
    dsimp [SetFamily.number_of_hyperedges]
    dsimp [P]

    have disj: Disjoint (Finset.filter (λ s => SF.sets s ∧ Q s) SF.ground.powerset)  (Finset.filter (λ s => SF.sets s ∧ ¬Q s) SF.ground.powerset) :=
    by
      rw [Finset.disjoint_filter]
      intro x_1 a a_1
      simp_all only [ne_eq, gt_iff_lt, Finset.mem_powerset, not_true_eq_false, and_false, not_false_eq_true, P, Q]

    have unon: (Finset.filter (λ s => SF.sets s) SF.ground.powerset) = (Finset.filter (fun s => (SF.sets s ∧ Q s)) SF.ground.powerset) ∪ (Finset.filter (fun s => (SF.sets s ∧ ¬Q s)) SF.ground.powerset) :=
    by
      simp_all only [ne_eq, gt_iff_lt, P, Q]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      simp_all only [Subtype.mk.injEq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
        Finset.card_singleton, Nat.reduceAdd, P]
      ext a : 1
      simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, P]
      apply Iff.intro
      · intro a_1
        simp_all only [true_and, P]
        obtain ⟨left, right⟩ := a_1
        tauto
      · intro a_1
        cases a_1 with
        | inl h_1 => simp_all only [and_self, P]
        | inr h_2 => simp_all only [and_self, P]

    have h_nat : (Finset.filter (λ s => SF.sets s) SF.ground.powerset).card
             = (Finset.filter (λ s => SF.sets s ∧ Q s) SF.ground.powerset).card
               + (Finset.filter (λ s => SF.sets s ∧ ¬ Q s) SF.ground.powerset).card :=
    by
      simp_all only [ne_eq, gt_iff_lt, Finset.card_union_of_disjoint, P, Q]

    simp_all only [ne_eq, gt_iff_lt, Finset.card_union_of_disjoint, Nat.cast_add, P, Q]

  show SF.number_of_hyperedges < ∑ x_1 ∈ Finset.filter SF.sets SF.ground.powerset, (({x.val, y.val} ∩ x_1).card : ℤ)

  dsimp [SetFamily.number_of_hyperedges]

  --linarithに使うもの
  --補題 lemma equal_one_implies_zero (SF: ClosureSystem α) [DecidablePred SF.sets] (x y :SF.ground)
  --補題 lemma two_superior_implies_notone_positive (SF: ClosureSystem α) [DecidablePred SF.sets] (x y :SF.ground) (neq: x ≠ y):
  --superior SF ({x.val,y.val}:Finset α) →
  --(Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card ≠ 1) SF.ground.powerset).card <
  --∑ x_1 ∈ Finset.filter (fun s => SF.sets s ∧ ({x.val, y.val} ∩ s).card ≠ 1) SF.ground.powerset, (({x.val, y.val} ∩ x_1).card:Int)

  suffices  (Finset.filter (fun s => (P s ∧ Q s)) SF.ground.powerset).card + (Finset.filter (fun s => (P s ∧ ¬Q s)) SF.ground.powerset).card < ∑ x_1 ∈ Finset.filter SF.sets SF.ground.powerset, (({x.val, y.val} ∩ x_1).card : ℤ) from
  by
    rw [←separate_card] at this
    convert this

  suffices (Finset.filter (fun s => (P s ∧ Q s)) SF.ground.powerset).card + (Finset.filter (fun s => (P s ∧ ¬Q s)) SF.ground.powerset).card < ∑ s ∈ (SF.ground.powerset.filter (fun s => (P s) ∧ (Q s))), ↑({x.val, y.val} ∩ s).card + ∑ s ∈ (SF.ground.powerset.filter (fun s => (P s ∧ ¬ (Q s)))), ↑({x.val, y.val} ∩ s).card from
  by
    rw [←notone_sum] at this
    norm_cast

  -- not Qのほうの補題
  let tsin := two_superior_implies_notone_positive SF x y neq sp

  -- Qが成立するほうの補題
  let eoiz := equal_one_implies_zero SF x y

  norm_cast at tsin
  --norm_cast at eoiz
  simp_all only [P,Q]
  linarith

lemma com4 (A B C D : ℕ) : A + B + C + D = D + B + C + A := by
  ring

lemma number_of_hyperedges_pair_card (SF: ClosureSystem α) [DecidablePred SF.sets] (x y :SF.ground) (neq: x ≠ y):
  ↑(Finset.filter (fun s => SF.sets s) SF.ground.powerset).card =
  ↑(Finset.filter (fun s => SF.sets s ∧ ↑x ∉ s ∧ ↑y ∉ s) SF.ground.powerset).card +
    ↑(Finset.filter (fun s => SF.sets s ∧ ↑x ∈ s ∧ ↑y ∉ s) SF.ground.powerset).card +
    ↑(Finset.filter (fun s => SF.sets s ∧ ↑x ∉ s ∧ ↑y ∈ s) SF.ground.powerset).card +
    ↑(Finset.filter (fun s => SF.sets s ∧ ↑x ∈ s ∧ ↑y ∈ s) SF.ground.powerset).card :=
by
  -- `SF.sets s` を `x ∈ s` と `x ∉ s` に分ける
  have h1 := add_compl_card SF.ground.powerset (fun s => SF.sets s) (fun s => x.val ∈ s)

  -- `x ∈ s` の部分を `y ∈ s` と `y ∉ s` に分ける
  have h2 := add_compl_card (Finset.filter (fun s => SF.sets s ∧ x.val ∈ s) SF.ground.powerset)
    (fun s => True) (fun s => y.val ∈ s)

  -- `x ∉ s` の部分を `y ∈ s` と `y ∉ s` に分ける
  have h3 := add_compl_card (Finset.filter (fun s => SF.sets s ∧ x.val ∉ s) SF.ground.powerset)
    (fun s => True) (fun s => y.val ∈ s)

  -- `Finset.card` の等式を適用
  rw [Finset.filter_filter] at h2 h3
  rw [h1]
  simp at h2
  rw [h2]
  simp at h3
  rw [h3]
  rw [Finset.filter_filter]
  rw [Finset.filter_filter]
  rw [Finset.filter_filter]
  rw [Finset.filter_filter]
  ring_nf
  rw [com4]

  congr
  · ext s
    simp only [and_assoc]
  · ext s
    simp_all only [ne_eq]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    simp_all only [Subtype.mk.injEq]
    apply Iff.intro
    · intro a
      simp_all only [not_false_eq_true, and_self]
    · intro a
      simp_all only [and_self, not_false_eq_true]
  · ext s
    simp only [and_assoc]
  · ext s
    simp_all only [ne_eq]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    simp_all only [Subtype.mk.injEq]
    apply Iff.intro
    · intro a
      simp_all only [and_self]
    · intro a
      simp_all only [and_self]

--{x,y}のペア次数とxの次数とyの次数の関係。今は補題として使っていないが、これを使って、pair優位の定理を証明できたかも。
theorem two_superior_pair_eq_pair_degree (SF: ClosureSystem α) [DecidablePred SF.sets] (x y :SF.ground) (neq: x ≠ y):
  ((Finset.filter (fun s => (SF.sets s ∧ {x.val,y.val} ⊆ s)) SF.ground.powerset).card:ℤ) - (Finset.filter (fun s => (SF.sets s ∧ {x.val,y.val} ∩ s = ∅)) SF.ground.powerset).card + SF.number_of_hyperedges = SF.degree x.val + SF.degree y.val  :=
by
  let n00 := (Finset.filter (fun s => (SF.sets s ∧ x.val ∉ s ∧ y.val ∉ s)) SF.ground.powerset).card
  let n10 := (Finset.filter (fun s => (SF.sets s ∧ x.val ∈ s ∧ y.val ∉ s)) SF.ground.powerset).card
  let n01 := (Finset.filter (fun s => (SF.sets s ∧ x.val ∉ s ∧ y.val ∈ s)) SF.ground.powerset).card
  let n11 := (Finset.filter (fun s => (SF.sets s ∧ x.val ∈ s ∧ y.val ∈ s)) SF.ground.powerset).card

  have h11: (Finset.filter (fun s => (SF.sets s ∧ {x.val,y.val} ⊆ s)) SF.ground.powerset).card = n11 :=
  by
    simp_all only [ne_eq, gt_iff_lt,Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, CharP.cast_eq_zero, n11]
    have :∀ s:Finset α, s ∈ SF.ground.powerset → (x.val ∈ s ∧ y.val ∈ s ↔ {x.val,y.val} ⊆ s) :=
    by
      intro s hs
      simp_all only [ne_eq, gt_iff_lt, Finset.mem_powerset, Finset.subset_iff, Finset.not_mem_empty]
      apply Iff.intro
      · intro h
        simp_all only [ne_eq, gt_iff_lt, Finset.not_mem_empty, Finset.not_mem_singleton, Finset.mem_insert, Finset.mem_singleton]
        intro x_1 a
        cases a with
        | inl h =>
          subst h
          simp_all only
        | inr h_1 =>
          subst h_1
          simp_all only
      · intro h
        simp_all only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, and_self, n11]
    simp_all only [Finset.mem_powerset, n11]
    congr 1
    ext a : 1
    simp_all only [Finset.mem_filter, Finset.mem_powerset, and_congr_right_iff, implies_true]

  have h10: SF.degree x.val = n10 + n11 :=
  by
    dsimp [SetFamily.degree]
    dsimp [n10,n11]
    let acc := add_compl_card SF.ground.powerset (fun s => SF.sets s∧ x.val ∈ s ) (fun s => y.val ∈ s)
    rw [add_comm]
    simp_all only [ne_eq, Nat.cast_add, n10, n11, acc]
    congr
    · simp only [and_assoc]
    · ext x : 2
      apply Iff.intro
      · intro a
        simp_all only [not_false_eq_true, and_self]
      · intro a
        simp_all only [and_self, not_false_eq_true]
  have h01: SF.degree y.val = n01 + n11 :=
  by
    dsimp [SetFamily.degree]
    dsimp [n01,n11]
    let acc := add_compl_card SF.ground.powerset (fun s => SF.sets s∧ y.val ∈ s ) (fun s => x.val ∈ s)
    simp_all only [ne_eq, Nat.cast_add, n01, n11, acc]
    have : ∀ s:Finset α, ↑(Finset.filter (fun s => (SF.sets s ∧ y.val ∈ s) ∧ x.val ∉ s) SF.ground.powerset).card =
       ↑(Finset.filter (fun s => SF.sets s ∧ ↑x ∉ s ∧ ↑y ∈ s) SF.ground.powerset).card :=
    by
      intro s
      congr
      ext z : 2
      apply Iff.intro
      · intro a
        simp_all only [not_false_eq_true, and_self]
      · intro a
        simp_all only [and_self, not_false_eq_true]
    rw [this]
    norm_cast
    have :(Finset.filter (fun s => (SF.sets s ∧ ↑y ∈ s) ∧ ↑x ∈ s) SF.ground.powerset).card
      =  (Finset.filter (fun s => SF.sets s ∧ ↑x ∈ s ∧ ↑y ∈ s) SF.ground.powerset).card :=
    by
      congr
      ext z : 2
      apply Iff.intro
      · intro a
        simp_all only [ne_eq, gt_iff_lt, Finset.mem_filter, Finset.mem_powerset, and_self]
      · intro a
        simp_all only [ne_eq, gt_iff_lt, Finset.mem_filter, Finset.mem_powerset, and_self]
    rw [this]
    ring
    simp_all only [forall_const, n10, n01, n11]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    simp_all only [Subtype.mk.injEq]
    exact Finset.univ

  have h00: (Finset.filter (fun s => (SF.sets s ∧ {x.val,y.val} ∩ s = ∅)) SF.ground.powerset).card = n00 :=
  by
    simp_all only [ne_eq, gt_iff_lt, Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, CharP.cast_eq_zero, n00]
    have :∀ s:Finset α, s ∈ SF.ground.powerset → (x.val ∉ s ∧ y.val ∉ s ↔ {x.val,y.val} ∩ s = ∅) :=
    by
      intro s hs
      simp_all only [ne_eq, gt_iff_lt, Finset.mem_powerset, Finset.subset_iff, Finset.not_mem_empty]
      apply Iff.intro
      · intro h
        simp_all only [ne_eq, gt_iff_lt, Finset.not_mem_empty, Finset.not_mem_singleton, Finset.mem_insert, Finset.mem_singleton]
        simp_all only [forall_eq_or_imp, forall_eq, not_false_eq_true, Finset.insert_inter_of_not_mem,
          Finset.singleton_inter_of_not_mem, n10, n01, n00, n11]
      · intro h
        simp_all only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, and_self, n00]
        constructor
        ·
          intro a
          simp_all only [Finset.insert_inter_of_mem, Finset.insert_ne_empty]
        · intro a
          rw [← @Finset.disjoint_iff_inter_eq_empty] at h
          simp_all only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, not_true_eq_false, and_false, n10,
            n01, n00, n11]

    simp_all only [Finset.mem_powerset, n00]
    congr 1
    ext a : 1
    simp_all only [Finset.mem_filter, Finset.mem_powerset, and_congr_right_iff, implies_true]

  have hn: SF.number_of_hyperedges = n00 + n10 + n01 + n11 :=
  by
    dsimp [SetFamily.number_of_hyperedges]
    dsimp [n00,n10,n01,n11]
    simp_all only [ne_eq, gt_iff_lt, Finset.card_union_of_disjoint, n10, n01, n00, n11]
    rw [number_of_hyperedges_pair_card]
    simp_all only [Nat.cast_add, n00, n01, n11, n10]
    norm_cast
    simp_all only [ne_eq, not_false_eq_true, n00, n01, n11, n10]

  have dy: SF.degree y.val = n01 + n11 :=
  by
    simp_all only [ne_eq, n10, n01, n00, n11]
  have dx: SF.degree x.val = n10 + n11 :=
  by
    simp_all only [ne_eq, n10, n01, n00, n11]
  rw [dx,dy]
  rw [h11,h00]
  linarith
