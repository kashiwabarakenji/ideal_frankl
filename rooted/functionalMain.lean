--functionalの議論の主定理functional_family_average_rareが収められている。各段階の重要な定理もここが親。
--functionalCommon.leanは、基本的な定義をまとめたもの。Setupもここで定義。
--前順序Setupに関しては、functionalTreePreorderで議論。
--Setup2は、Setupで導入されたsetoid上に半順序を導入したもの。functionalTreePartialOrderで定義。
--前順序Setup2は、SetupとSetup2は仮定の強さは変わらない。
--functionalTreeIdealは、閉集合族としてのSetup2の議論。
--Setup_spoは、functionalSPOでの定義。前順序が出てきてないので、より抽象化している。
--ただ、いまから考えると、もともとのfを同じ要素に移すことを許していれば、
--SetupとSetup_spoの違いを考える必要がなかったのかも。
--functionalIdealrareもSetup_spoの枠組み。
--Setup_spo2は、親がひとつだということを考慮した枠組み。Setup_spoよりも少し強くなっている。
--本来の条件は、Setup_spo2なのだか、もうちょっと弱くても成り立つ定理はSetup_spoで証明。
--functionalTraceIdealは、traceすることで半順序の枠組みの定理に帰着させている。
--functionalPartialのシリーズは、半順序の枠組みの定理。詳しくはそちらを参照。
--Setupは、名前を変えるとするとSetup_preか？
--Setup_spoは、名前を変えなくて良い。
--Setup_poは、そのままでよい。

--リファクタリングをするとすると、最初のvalidの条件をなくして、定式化したほうがよい。
--すると、Setup_spoがいらなくなるのでは。
import Mathlib.Data.Finset.Basic
import Init.WF
import Mathlib.Order.WellFoundedSet
import LeanCopilot
import rooted.CommonDefinition
import rooted.functionalCommon
import rooted.functionalTraceIdeal2
import rooted.functionalPartialOne
import rooted.functionalDirectProduct2

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

--setup_po_average_rareの証明の中に書いてあったベースケースを補題として独立させた。
--o4-mini-highで書き直したが短くはなってない。
lemma setup_po_average_rare_card_one (t : Setup_po α) (card1 : t.V.card = 1) :
  (po_closuresystem t).toSetFamily.normalized_degree_sum ≤ 0 := by
  let ceo := (@card_eq_one _ t.V).mp card1
  obtain ⟨x, _hx⟩ := ceo

  -- normalized_degree_sum の定義を展開して簡約
  dsimp [ SetFamily.normalized_degree_sum]
  simp

  -- hyperedge の集合を ∅ と t.V に絞れる
  have h_sets : ∀ ss : Finset α,
      (po_closuresystem t).sets ss ↔ ss = ∅ ∨ ss = t.V := by
    intro ss
    constructor
    · intro h
      have hsub : ss ⊆ t.V := by
        dsimp [po_closuresystem] at h
        exact h.1
      have : ss = ∅ ∨ ss = t.V := by
        --subst card1
        simp_all only
          [Finset.card_singleton,
           Finset.subset_singleton_iff,
           Nat.lt_one_iff,
           card_eq_zero,
           card_eq_one]
      exact this
    · intro h
      cases h
      case inl hl =>
        -- ss = ∅ の場合
        rw [hl]
        dsimp [po_closuresystem]
        simp
      case inr hr =>
        -- ss = {x} の場合
        rw [hr]
        simp_all only
          [Finset.card_singleton,
           Finset.subset_singleton_iff,
           Nat.lt_one_iff,
           card_eq_zero,
           card_eq_one]
        subst hr
        simp [po_closuresystem]
        simp_all only [Finset.mem_singleton, le_refl, imp_self, implies_true, and_self]

  -- total_size_of_hyperedges = 1
  have h_total : (po_closuresystem t).total_size_of_hyperedges = 1 := by
    dsimp [po_closuresystem] at h_sets
    dsimp [SetFamily.total_size_of_hyperedges]
    simp_all only [h_sets]
    -- フィルタ結果が {∅, {x}} になる
    have h :
      filter (fun s => s = ∅ ∨ s = {x}) ({x} : Finset α).powerset = {∅, {x}} := by
      simp_all only
        [Finset.subset_singleton_iff,
         Finset.mem_singleton,
         Nat.lt_one_iff,
         card_eq_zero,
         card_eq_one]
      simp_all only [singleton_inj, exists_eq', Subtype.forall, Finset.mem_singleton, le_refl, imp_self, implies_true,
        and_true]
      ext a : 1
      simp_all only [mem_filter, Finset.mem_powerset, Finset.subset_singleton_iff, and_self, Finset.mem_insert,
        Finset.mem_singleton]

    dsimp [po_closuresystem]
    simp_all only [Finset.card_singleton, Finset.subset_singleton_iff, Subtype.forall, Finset.mem_singleton, le_refl,
      imp_self, implies_true, and_true, Finset.card_empty, sum_insert_of_eq_zero_if_not_mem, sum_singleton,
      Nat.cast_one]

  -- number_of_hyperedges = 2
  have h_num : (po_closuresystem t).number_of_hyperedges = 2 := by
    dsimp [SetFamily.number_of_hyperedges]
    -- ground.powerset = {∅, {x}}
    have : (po_closuresystem t).ground.powerset = {∅, {x}} := by
      dsimp [po_closuresystem] at h_sets
      simp_all only
        [Finset.subset_singleton_iff,
         Finset.mem_singleton,
         Nat.lt_one_iff,
         card_eq_zero,
         card_eq_one]
      dsimp [po_closuresystem]
      rw [_hx]
      exact rfl
    rw [this]
    dsimp [po_closuresystem]
    -- フィルタ後も {∅, {x}}
    have h :
      filter
        (fun ss =>
          ss ⊆ t.V ∧
          ∀ v : { x // x ∈ t.V }, v.val ∈ ss → ∀ w : { x // x ∈ t.V }, t.po.le w v → w.val ∈ ss)
        ({∅, {x}} : Finset (Finset α)) = {∅, {x}} := by
      simp_all only
        [Finset.subset_singleton_iff,
         Finset.mem_singleton,
         Nat.lt_one_iff,
         card_eq_zero,
         card_eq_one]
      simp [filter_true_of_mem]
      simp_all only [singleton_inj, exists_eq', Finset.mem_singleton, le_refl, imp_self, implies_true, and_true]
      simp [filter_true_of_mem]
    simp_all only
      [Finset.subset_singleton_iff,
       Finset.mem_singleton,
       Nat.lt_one_iff,
       card_eq_zero,
       card_eq_one]
    rfl

  -- 最後に元の通りに rw → Int.ge_of_eq で終わり
  rw [h_total, h_num]
  apply Int.ge_of_eq
  apply congrArg (HMul.hMul 2)
  apply congrArg Nat.cast
  exact card1
  -- 台集合が１要素なので，x を取る

--半順序setup_poに関するnormalized_degree_sumが非正になる定理。
theorem setup_po_average_rare (s_orig:Setup_po α): (po_closuresystem s_orig).normalized_degree_sum ≤ 0 :=
by
  let P : ℕ → Prop := fun n =>
    ∀ t : Setup_po α,
      t.V.card = n →
      (po_closuresystem t).toSetFamily.normalized_degree_sum ≤ 0

  ------------------------------------------------------------------
  --  P n をすべての n について示す
  ------------------------------------------------------------------
  have hP : ∀ n, P n := by
    intro n
    -- strong recursion on `n`
    induction' n using Nat.strongRec with n ih
    intro t ht_card

    by_cases h_le_one : t.V.card ≤ 1
    · -- baseケース。証明を外に出しても良い。
      have : t.V.card = 1 :=
      by
        exact le_antisymm h_le_one (one_le_card.mpr t.nonemp)
      exact setup_po_average_rare_card_one t this

    ----------------------------------------------------------------
    -- 帰納ケース  |V| ≥ 2
    ----------------------------------------------------------------
    · have nontriv : 2 ≤ t.V.card := Nat.succ_le_of_lt (Nat.lt_of_not_ge h_le_one)

      -- quotient のクラス数で場合分け
      by_cases h_one : numClasses (proj_setoid t) = 1

      --------------------------------------------------------------
      --  (1) クラス数 = 1  ― Trace で ground を減らす
      --------------------------------------------------------------
      · -- 最大元を 1 つ取る
        obtain ⟨x, hx⟩ := t.nonemp --quotient_exists t   -- プロジェクト側の補題名に合わせて調整
        let mx := proj_max t ⟨x, hx⟩
        have hmx : po_maximal t mx := by
          exact proj_max_maximal t ⟨x, hx⟩

        -- nds の比較
        have h_nds_le_trace :=
          normalized_degree_sum_gt t h_one mx hmx nontriv
        -- ground が 1 減る
        have h_card_lt :
            (po_trace t mx hmx nontriv).V.card < t.V.card :=
          trace_one_ground_card t mx hmx nontriv
        -- 強い帰納法の仮定で trace 側の nds ≤ 0
        have h_nds_trace :=
          ih _ (by
                have : (po_trace t mx hmx nontriv).V.card < n := by
                  -- `ht_card : t.V.card = n` を使って < n に変形
                  have := h_card_lt
                  simpa [ht_card] using this
                exact this) _ (by
                  -- trace の card = card,  reflexive rewrite
                  rfl)
        -- 連鎖律で結論
        exact h_nds_le_trace.trans h_nds_trace

      --------------------------------------------------------------
      --  (2) クラス数 ≥ 2 ― comp/excl で分割
      --------------------------------------------------------------
      · -- ≥ 2 に昇格させる
        have h_ge_two : numClasses (proj_setoid t) ≥ 2 := by
          -- 1 ではない & 正  →  2 以上
          have h_pos : 0 < numClasses (proj_setoid t) := numClasses_pos t
          have : 1 ≤ numClasses (proj_setoid t) := Nat.succ_le_of_lt h_pos
          apply Nat.succ_le_of_lt
          exact Nat.lt_of_le_of_ne h_pos fun a => h_one (id (Eq.symm a))

        -- 適当なクラス q を 1 つ取る（存在はクラシカルに）
        obtain  ⟨q : Quotient (proj_setoid t)⟩ := quotient_exists t

        -- ground が確かに減る
        have h_comp_card :=
          directProduct_comp_excel_ground_c t q h_ge_two
        have h_excl_card :=
          directProduct_comp_excel_ground_e t q h_ge_two

        -- IH を comp と excl に適用
        have h_nds_comp :
            (po_closuresystem (comp_po t q)).toSetFamily.normalized_degree_sum ≤ 0 := by
          have h_lt : (comp_po t q).V.card < n := by
            have : (comp_po t q).V.card < t.V.card := h_comp_card
            simpa [ht_card] using this
          exact (ih _ h_lt) _ rfl

        have h_nds_excl :
            (po_closuresystem (excl_po t q h_ge_two)).toSetFamily.normalized_degree_sum ≤ 0 := by
          have h_lt : (excl_po t q h_ge_two).V.card < n := by
            have : (excl_po t q h_ge_two).V.card < t.V.card := h_excl_card
            simpa [ht_card] using this
          exact (ih _ h_lt) _ rfl

        -- comp/excl を貼り合わせて元の nds ≤ 0
        exact directProduct_nds t q h_ge_two h_nds_comp h_nds_excl
  exact hP (#s_orig.V) s_orig rfl

--Setup_spo2の主定理。functionalMainで利用している。
--ここだけ初期のsとして、sじゃなくてs₀をつかっているので注意。帰納法でsが動くため。
--trace_ideal_nds_increaseを使っているので、仮定は、Setup_spoでなくて、Setup_spo2である必要がある。
theorem setup_spo2_average_rare (s₀ :Setup_spo2 α): (spo_closuresystem s₀.toSetup_spo).normalized_degree_sum ≤ 0 :=
by

  --この定理の証明は、excessの値に関する強い帰納法。
  --ベースケースであるexcess=0の場合が、setup_po_average_rareに相当。
  --それに相当するということを証明するのに、excess_zeroを使う。

  --lemma trace_excess_decrease (s: Setup_spo2 α) (x: s.V) (hx: (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2) :
  --excess (setup_trace_spo2 s x hx) = excess s - 1 := by
  --を使って、excessが減っていくことを示す。
  --theorem trace_ideal_nds_increase (s: Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2)
  --ChatGPT o3に全体の構造を設計してもらった。WellFoundedOnを使って証明。
  let r : Setup_spo2 α → Setup_spo2 α → Prop :=
  fun s t => excess s.toSetup_spo < excess t.toSetup_spo

  have wf_r : WellFounded r := by simpa [r] using
    (measure (fun s : Setup_spo2 α => excess s.toSetup_spo)).wf

  /-
  let r : Setup_spo2 α → Setup_spo2 α → Prop := fun s t => excess s.toSetup_spo < excess t.toSetup_spo
  have wf_r : WellFounded r := (measure fun s => excess s.toSetup_spo).wf
  -/
  let wf_on : (univ : Set (Setup_spo2 α)).WellFoundedOn r :=
    WellFounded.wellFoundedOn wf_r

  apply Set.WellFoundedOn.induction wf_on (x := s₀) (hx := Set.mem_univ s₀)
  intro s mem_s ih

  by_cases h0 : excess s.toSetup_spo = 0
  · --基底ケース
    -- 定理 excess_zero で全クラスがサイズ1
    have h1 : ∀ q, (classOf s.toSetup_spo q).card = 1 := by
      apply excess_zero s.toSetup_spo
      exact h0
    -- これで Setup_po を作り，ベース補題を適用
    let s_po := po_ideal_system_from_allone _ h1
    let spa := setup_po_average_rare s_po
    rw [←po_ideal_system_eq]
    simp_all only [not_lt_zero', IsEmpty.forall_iff, implies_true, ge_iff_le]
    exact spa

  · -- 帰納ステップ：excess s > 0 の場合
    -- 1) excess s ≠ 0 から 0 < excess s を得る
    have hpos : 0 < excess s.toSetup_spo := by
      simp_all only [Set.mem_univ, gt_iff_lt, ge_iff_le, forall_const, r]
      omega

    -- 2) ∃ q, classOf の大きさ ≥ 2 を得る
    obtain ⟨q, hq⟩ := exists_q_card_ge_two_of_excess_pos s.toSetup_spo hpos

    -- 3) trace して新しい構造体 s' を作る
    have :@Quotient.mk _ s.setoid q.out = q :=
      by
        simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true, ge_iff_le, Quotient.out_eq]
    rw [←this] at hq

    let s' := setup_trace_spo2 s q.out hq

    -- 4) excess は１だけ減る
    have h_ex_s' : excess s'.toSetup_spo = excess s.toSetup_spo - 1 :=
      trace_excess_decrease s.toSetup_spo q.out hq

    -- 5) normalized_degree_sum は増える
    have h_nds :
      (spo_closuresystem s.toSetup_spo).normalized_degree_sum
        ≤ (spo_closuresystem s'.toSetup_spo).normalized_degree_sum :=
    by
      dsimp [s']
      exact trace_ideal_nds_increase2 s q.out hq
      /-
      --let tin := trace_ideal_nds s.toSetup_spo q.out hq
      rw [setup_trace_spo2_lem ]
      rw [trace_ideal_nds s.toSetup_spo q.out hq]
      exact trace_ideal_nds_increase s q.out hq
      -/

    -- 6) s' < s（r s' s） を示す
    have h_rel : r s' s := by
      dsimp [r]
      -- h_ex_s' : excess s' = excess s - 1, hpos : 0 < excess s
      -- から Nat.sub_lt を使うのが簡単
      rw [h_ex_s']
      simp_all only [Set.mem_univ, gt_iff_lt, ge_iff_le, forall_const, Quotient.out_eq, tsub_lt_self_iff,
        Nat.lt_one_iff, pos_of_gt, and_self, s', r]

    -- 7) 帰納仮定を s' に適用（s' ∈ univ は by simp）
    have ih_s' :
      (spo_closuresystem s'.toSetup_spo).normalized_degree_sum ≤ 0 :=
      ih s' (by simp) h_rel

    -- 8) まとめて calc で結論
    calc
      (spo_closuresystem s.toSetup_spo).normalized_degree_sum
          ≤ (spo_closuresystem s'.toSetup_spo).normalized_degree_sum := h_nds
      _ ≤ 0 := ih_s'


--setupを使った形の主定理。この定理はsetup_spo2_average_rareに帰着させるので帰納法は必要なくて、直接証明可能。
lemma setup_average_rare (s:Setup α): (pre_closuresystem s).normalized_degree_sum ≤ 0 :=
by
  --spo2_average_rareから証明する。
  --setup2_induces_spoを使って、対応するSetup_spo2が得られる。spo2からclosuresystemを生成するには、spo_closuresystem
  --trace_ideal_ndsはidealがひとしければndsも等しいという定理。
  --theorem Setup_spo_eq_PartialOrder (s: Setup2 α)  : pre2_closuresystem s = spo_closuresystem (setup_setupspo s)
  --が利用するメインの定理。
  --pre2_closuresystem (s: Setup2 α): ClosureSystem となる。pre_closuresystemとの違いはSetup2のところか。
  --theorem Preorder_eq_PartialOrder (s: Setup2 α)  :  pre_closuresystem s.toSetup = pre2_closuresystem s  := by
  --という定理もあった。
  let s2 :=  (Setup_to_Setup2 s)
  let s_spo := setup2_induces_spo s2  --setup_spo2_average_rareに帰着させるためspoに埋め込み。
  have : s2.toSetup = s :=
  by
    rfl
  rw [←this]
  rw [Preorder_eq_PartialOrder s2]
  rw [Setup_spo_eq_PartialOrder s2]
  exact setup_spo2_average_rare s_spo

--全体の主定理。setupを使わない形。
theorem functional_family_average_rare (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty) :
  (rootedsetToClosureSystem (rootedset_onestem_eachvertex_V V f valid nonemp)).normalized_degree_sum ≤ 0 :=
by
  let rs := rootedset_onestem_eachvertex_V V f valid nonemp
  set pre := size_one_preorder V f valid nonemp with h_pre
  set st := @setoid_preorder V pre with h_st
  let s := Setup.mk V nonemp f valid pre h_pre st h_st
  let sns := setup_average_rare s
  rw [pre_closuresystem_eq_lem] at sns  --ここで、pre_closuresystem2を経由するのは必要。
  dsimp [pre_closuresystem2] at sns
  dsimp [rootedset_from_setup] at sns
  exact sns
