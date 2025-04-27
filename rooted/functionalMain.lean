import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Finset.Powerset
--import Mathlib.Data.Set.Function
--import Mathlib.Data.Fintype.Basic
--import Mathlib.Order.Defs.PartialOrder
--import Mathlib.Order.Cover
--import Mathlib.Tactic
import Init.WF
import Mathlib.Order.WellFoundedSet
import LeanCopilot
import rooted.CommonDefinition
--import rooted.ClosureMinors
--import rooted.Dominant
--import rooted.FamilyLemma
import rooted.functionalCommon
--import rooted.StemSizeOne
import rooted.functionalTraceIdeal2


open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

lemma setup_po_average_rare (s:Setup_po α): (partialorder_ideal_system s).normalized_degree_sum ≤ 0 :=
by
  sorry

--ここだけsじゃなくてs₀をつかっているので注意。
lemma setup_spo2_average_rare (s₀ :Setup_spo2 α): (spo_closuresystem s₀.toSetup_spo).normalized_degree_sum ≤ 0 :=
by

  --この定理の証明は、excessの値に関する帰納法。
  --ベースケースであるexcess=0の場合が、setup_po_average_rareに相当。
  --それに相当するということを証明するのに、excess_zeroを使う。

  --lemma trace_excess_decrease (s: Setup_spo2 α) (x: s.V) (hx: (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2) :
  --excess (setup_trace_spo2 s x hx) = excess s - 1 := by
  --を使って、excessが減っていくことを示す。
  --theorem trace_ideal_nds_increase (s: Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2)
  --ChatGPT o3に全体の構造を設計してもらった。WellFoundedOnを使って証明。
  let r : Setup_spo2 α → Setup_spo2 α → Prop := fun s t => excess s < excess t
  have wf_r : WellFounded r := (measure fun s => excess s).wf
  let wf_on : (univ : Set (Setup_spo2 α)).WellFoundedOn r :=
    WellFounded.wellFoundedOn wf_r

  apply Set.WellFoundedOn.induction wf_on (x := s₀) (hx := Set.mem_univ s₀)
  intro s mem_s ih

  by_cases h0 : excess s = 0
  · --基底ケース
    -- 定理 excess_zero で全クラスがサイズ1
    have h1 : ∀ q, (classOf s.toSetup_spo q).card = 1 := by
      apply excess_zero s
      exact h0
    -- これで Setup_po を作り，ベース補題を適用
    let s_po := po_ideal_system_from_allone _ h1
    let spa := setup_po_average_rare s_po
    rw [←po_ideal_system_eq]
    simp_all only [not_lt_zero', IsEmpty.forall_iff, implies_true, ge_iff_le]
    exact spa

  · -- 帰納ステップ：excess s > 0 の場合
    -- 1) excess s ≠ 0 から 0 < excess s を得る
    have hpos : 0 < excess s := by
      simp_all only [Set.mem_univ, gt_iff_lt, ge_iff_le, forall_const, r]
      omega

    -- 2) ∃ q, classOf の大きさ ≥ 2 を得る
    obtain ⟨q, hq⟩ := exists_q_card_ge_two_of_excess_pos s hpos

    -- 3) trace して新しい構造体 s' を作る
    have :@Quotient.mk _ s.setoid q.out = q :=
      by
        simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true, ge_iff_le, Quotient.out_eq]
    rw [←this] at hq

    let s' := setup_trace_spo2 s q.out hq

    -- 4) excess は１だけ減る
    have h_ex_s' : excess s' = excess s - 1 :=
      trace_excess_decrease s q.out hq

    -- 5) normalized_degree_sum は増える
    have h_nds :
      (spo_closuresystem s.toSetup_spo).normalized_degree_sum
        ≤ (spo_closuresystem s'.toSetup_spo).normalized_degree_sum :=
    by
      dsimp [s']
      rw [trace_ideal_nds]
      exact trace_ideal_nds_increase s q.out hq

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


--setupを使った形の主定理。この定理は帰納法は必要なくて、直接証明可能。
lemma setup_average_rare (s:Setup α): (preorder_ideal_system s).normalized_degree_sum ≤ 0 :=
by
  --spo2_average_rareから証明する。
  --setup2_induces_spoを使って、対応するSetup_spo2が得られる。spo2からclosuresystemを生成するには、spo_closuresystem
  --trace_ideal_ndsはidealがひとしければndsも等しいという定理。
  --theorem Setup_spo_eq_PartialOrder (s: Setup2 α)  : setoid_ideal_ClosureSystem s = spo_closuresystem (setup_setupspo s)
  --が利用するメインの定理。
  --setoid_ideal_ClosureSystem (s: Setup2 α): ClosureSystem となる。preorder_ideal_systemとの違いはSetup2のところか。
  --theorem Preorder_eq_PartialOrder (s: Setup2 α)  :  preorder_ideal_system s.toSetup = setoid_ideal_ClosureSystem s  := by
  --という定理もあった。
  let s2 :=  (Setup_to_Setup2 s)
  let s_spo := setup2_induces_spo s2
  have : s2.toSetup = s :=
  by
    rfl
  rw [←this]
  rw [Preorder_eq_PartialOrder s2]
  rw [Setup_spo_eq_PartialOrder s2]
  exact setup_spo2_average_rare s_spo

--主定理。setupを使わない形。
theorem functional_family_average_rare (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty) :
  (rootedsetToClosureSystem (rootedset_onestem_eachvertex_V V f valid nonemp)).normalized_degree_sum ≤ 0 :=
by
  let rs := rootedset_onestem_eachvertex_V V f valid nonemp
  set pre := size_one_preorder V f valid nonemp with h_pre
  set st := @setoid_preorder V pre with h_st
  let s := Setup.mk V nonemp f valid pre h_pre st h_st
  let sns := setup_average_rare s
  rw [ideal_system_eq_lem] at sns
  dsimp [preorder_ideal_system2] at sns
  dsimp [rootedset_from_setup] at sns
  exact sns
