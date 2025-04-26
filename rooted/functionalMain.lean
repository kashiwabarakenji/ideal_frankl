import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Finset.Powerset
--import Mathlib.Data.Set.Function
--import Mathlib.Data.Fintype.Basic
--import Mathlib.Order.Defs.PartialOrder
--import Mathlib.Order.Cover
--import Mathlib.Tactic
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

lemma setup_spo2_average_rare (s:Setup_spo2 α): (spo_closuresystem s.toSetup_spo).normalized_degree_sum ≤ 0 :=

  --この定理の証明は、excessの値に関する帰納法。
  --ベースケースであるexcess=0の場合が、setup_po_average_rareに相当。
  --それに相当するということを証明するのに、excess_zeroを使う。

  --lemma trace_excess_decrease (s: Setup_spo2 α) (x: s.V) (hx: (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2) :
  --excess (setup_trace_spo2 s x hx) = excess s - 1 := by
  --を使って、excessが減っていくことを示す。
  --theorem trace_ideal_nds_increase (s: Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2)
  --ChatGPT o3に全体の構造を設計してもらうのがいいかも。
  Nat.strong_induction_on (excess s) fun k IH => by
    -- excess s = k と仮定
    have h_ex : excess s = k := by sorry

    -- cases k = 0, succ k'
    cases k with
    | zero =>
      -- ◯ 基底ケース: excess s = 0
      -- 定理 excess_zero で全クラスがサイズ1
      have h1 : ∀ q, (classOf s.toSetup_spo q).card = 1 := excess_zero s h_ex
      -- これで Setup_po を作り，ベース補題を適用
      let s_po := po_ideal_system_from_allone _ h1
      let spa := setup_po_average_rare s_po
      rw [←trace_ideal_nds ] at spa





    | succ k' =>
      -- ◯ 帰納ステップ: excess s = k' + 1 > 0
      have h_pos : 0 < excess s := by simpa [h_ex] using Nat.zero_lt_succ k'

      -- (補題) excess s > 0 から ∃ q, card ≥ 2
      obtain ⟨q, hq_card⟩ :=
        exists_q_card_ge_two_of_excess_pos s h_pos

      -- 1. trace すると excess が 1 減る
      have h_ex' : excess (setup_trace_spo2 s q.val hq_card) = k' := by
        simpa [h_ex] using trace_excess_decrease s q.val hq_card

      -- 2. trace すると normalized_degree_sum は増える
      have h_nds :
        (spo_closuresystem s.toSetup_spo).normalized_degree_sum ≤
        (spo_closuresystem (setup_trace_spo2 s q.val hq_card).toSetup_spo)
          .normalized_degree_sum :=
        trace_ideal_nds_increase s q.val hq_card

      -- 3. IH を適用（excess が k' に小さくなったケース）
      calc
        (spo_closuresystem s.toSetup_spo).normalized_degree_sum
          ≤ (spo_closuresystem (setup_trace_spo2 s q.val hq_card).toSetup_spo)
              .normalized_degree_sum := h_nds
        _ ≤ 0 := IH k' (by simpa [h_ex'] using Nat.succ_pos k') _

      -- IH の引数 “_” には、setup_trace_spo2 s q.val hq_card : Setup_spo2 α
      -- という点が必要です

  -- end of strong_induction_on

--この定理は帰納法は必要なくて、直接証明可能。
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
