import Mathlib.Data.Finset.Basic --hiding eq_empty_of_subset_empty
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
--import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import Ideal.IdealSum
import Ideal.IdealNumbers
import Ideal.IdealDegreeOne
import Ideal.IdealFin
import LeanCopilot

--set_option maxHeartbeats 300000 --コメントアウトするとnumber_of_hyperedgesなどでエラー。原因追及が必要。
--set_option trace.Meta.Tactic.simp.rewrite true

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α]

lemma ineq_lem (k : ℕ) :
  (k + 1) * 2^(k + 1) + 2 * (k + 2) + (2 ^ (k + 1) - (k + 2)) = (2 ^ (k + 1) + 1) * (k + 2) := by
    have basic_ineq (n : ℕ) (h : 1 ≤ n) : 2^n≥n+1 :=
        by
          induction n with
          | zero =>
            -- 基底ケース: n = 0 は不適
            by_contra
            simp_all only [nonpos_iff_eq_zero, one_ne_zero]

          | succ k ih =>
          -- 帰納段階: n = k + 1 を証明
          -- 目標: 2^(k + 1) ≥ k + 2
          -- 2^(k + 1) = 2 * 2^k ≥ 2 * (k + 1) = k + 2
          have k_geq_0 : k ≥ 0 := by
              simp_all only [ le_add_iff_nonneg_left]

          rw [pow_succ 2 k]

          by_cases h1: k = 0
          case pos =>
            rw [h1]
            simp_all only [Nat.one_pow]
            omega
          case neg =>
          have hh1: k ≥ 1 := by
            simp_all only [ge_iff_le]
            omega
              -- 2^(k + 1) = 2 * 2^k
          have : 2 * 2^k ≥ 2 * (k + 1) := mul_le_mul_of_nonneg_left (ih hh1) (by norm_num)

          -- 2 * (k + 1) = k + 1 + k + 1 = 2k + 2 ≥ k + 2
          -- これは k ≥ 0 で常に成り立つ
          have : 2 * (k + 1) ≥ k + 2 := by
           calc
             2 * (k + 1) = k + 1 + k + 1 := by ring
             _ = (k + k) + (1 + 1) := by
               simp_all only [le_add_iff_nonneg_left]
               omega
             _ ≥ k + 2  := by
                simp_all only [le_add_iff_nonneg_left]
                omega
          simp_all only [ true_implies]
          omega
    have hh1: k + 1 ≥ 1 := by
      simp_all only [ge_iff_le]
      omega

    have add_sub_assoc (nn mm kk : ℕ) (h : mm ≥ kk) : nn + (mm - kk) = (nn + mm) - kk :=
      by
        rw [←Nat.add_sub_cancel' h]
        simp_all only [add_tsub_cancel_of_le]
        omega

    calc
    (k + 1) * 2^(k + 1) + 2 * (k + 2) + (2 ^ (k + 1) - (k + 2))
      = 2^(k + 1) * (k + 1) + 2 * (k + 2) + (2 ^ (k + 1) - (k + 2)) := by ring_nf
    _ = (2^(k + 1) * (k + 1) + 2*k + 4) + (2 ^ (k + 1) - (k + 2)) := by ring_nf
    _ = ((2^(k + 1) * (k + 1) + 2*k + 4) + 2 ^ (k + 1)) - (k + 2) := by
      rw [add_sub_assoc (2^(k + 1) * (k + 1) + 2*k + 4) (2 ^ (k + 1)) (k + 2) (basic_ineq (k+1) hh1)]
    _ = 2^(k + 1) * (k + 1) + 2^(k + 1) + 2*k + 4 - (k + 2) := by ring_nf
    _ = 2^(k + 1) * (k + 1 + 1) + 2 * k + 4 - (k + 2) := by ring_nf
    _ = 2^(k + 1) * (k + 2) + (2 * k + 4 - (k + 2)) := by
      simp_all only [ge_iff_le, Nat.reduceSubDiff]
      ring_nf
      omega
    _ = 2^(k + 1) * (k + 2) + (2 * (k + 2) - (k + 2)) := by ring_nf
    _ = 2^(k + 1) * (k + 2) + (k + 2) := by
      simp_all only [ge_iff_le, Nat.reduceSubDiff]
      ring_nf
      omega
    _ = (2^(k + 1) + 1) * (k + 2) := by
      ring_nf

def P (x:Nat) : Prop := x ≥ 2  ∧ ∀ (F: IdealFamily (Fin x)), F.ground.card = x → normalized_degree_sum F.toSetFamily ≤ 0

-- heartbeas問題に対応するために、証明を分離した。この部分は解決したが、他の部分でエラーになっている。
lemma total_eq_lem (n : Nat) (F : IdealFamily (Fin (n+1))) (v : Fin (n+1)) (v_in_ground : v ∈ F.ground)(ground_minus_v_none : ¬F.sets (F.ground \ {v})) (ground_ge_two : F.ground.card ≥ 2) (ground_card: F.ground.card = n + 1) (_: P n):
 ∑ x ∈ Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground \ {v}) (F.ground \ {v}).powerset, x.card + 1 =
  ∑ x ∈ Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground.erase v) (F.ground.erase v).powerset,
    if x = F.ground.erase v then x.card + 1 else x.card :=
  by
    have hv_equal: F.ground.erase v = F.ground \ {v} := by
      exact Finset.erase_eq F.ground v
    let gg := λ (s:Finset (Fin (n+1))) => if s = F.ground.erase v then s.card + 1 else s.card

    have lem_prop:∀ (s:Finset (Fin (n+1))), s ∈ (F.ground.erase v).powerset → ¬ ((F.sets s ∧ v ∉ s) ∧ s = F.ground.erase v) := by
      intro s _
      intro h

      obtain ⟨left, right⟩ := h
      rw [right] at left
      let left1 := left.1

      rw [hv_equal] at left1

      subst right
      simp_all only [not_true_eq_false]


    let leftset := Finset.filter (fun s => F.sets s ∧ v ∉ s) (F.ground.erase v).powerset
    let rightset := Finset.filter (fun s => s = F.ground.erase v) (F.ground.erase v).powerset

    have disjoint: leftset ∩ rightset = ∅ := by
      dsimp [leftset, rightset]
      rw [Finset.eq_empty_iff_forall_not_mem]
      by_contra h_contra
      rw [not_forall] at h_contra
      push_neg at h_contra
      obtain ⟨s, hs⟩ := h_contra
      rw [Finset.mem_inter] at hs
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_powerset] at hs
      have sg: s = F.ground.erase v := by
        simp_all only [hv_equal]
      have sgs: F.sets s := by
        subst sg
        simp_all only [Finset.mem_powerset]
      rw [sg] at sgs
      rw [hv_equal] at sgs
      exact ground_minus_v_none sgs

    have disjoint2: ∀ (s:Finset (Fin (n+1))), s ∈ (F.ground.erase v).powerset → ¬ ((F.sets s ∧ v ∉ s) ∧ s = F.ground.erase v) := by
      intro s _
      intro h
      obtain ⟨left, right⟩ := h
      rw [right] at left
      let left1 := left.1
      rw [hv_equal] at left1
      contradiction

    have sum_lem:  (Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground.erase v) (F.ground.erase v).powerset).sum gg
    = (Finset.filter (fun s => F.sets s ∧ v ∉ s) (F.ground.erase v).powerset).sum gg +  ( Finset.filter (fun s =>s = F.ground.erase v) (F.ground.erase v).powerset).sum gg:= by
      exact filter_sum_func (F.ground.erase v).powerset gg lem_prop
    rw [←hv_equal]
    rw [sum_lem]

    rw [filter_sum  (λ s => (F.sets s ∧ v ∉ s)) (λ s => s = F.ground.erase v) (F.ground.erase v).powerset disjoint2]

    dsimp [gg]
    simp_all only [Finset.mem_filter, Finset.mem_powerset]

    have sum_part1: ∑ x ∈ Finset.filter (fun s => F.sets s ∧ v ∉ s) (F.ground \ {v}).powerset, x.card = (∑ x ∈ Finset.filter (fun s => F.sets s ∧ v ∉ s) (F.ground \ {v}).powerset,
      if x = F.ground \ {v} then (F.ground \ {v}).card + 1 else x.card) := by
    --not F.sets(F.ground \ {v})なので、ifが満たされることはない。
      apply Finset.sum_congr rfl
      intro x hx
      have hx_filtered := Finset.mem_filter.mp hx
      by_cases hx_eq : x = F.ground \ {v}
      · case pos =>
        rw [hx_eq]
        simp
        rw [hx_eq] at hx_filtered
        have x_card: x.card = (F.ground \ {v}).card := by
          subst hx_eq
          simp only [not_true_eq_false]
        subst hx_eq
        simp_all only [not_true_eq_false]
      · case neg =>
        --x.card = if x = F.ground \ {v} then (F.ground \ {v}).card + 1 else x.card
        simp [hx_eq]

    have sum_part2: ∑ x ∈ (Finset.filter (fun s => s = F.ground.erase v) (F.ground.erase v).powerset), x.card = F.ground.card - 1 := by
      have h_filter : Finset.filter (λ s => s = F.ground.erase v) (F.ground.erase v).powerset = {F.ground.erase v} :=
        by
          ext s
          simp [Finset.mem_powerset, Finset.mem_filter]
          rw [Finset.subset_iff]
          intro hh
          intro x hx
          rw [Finset.mem_erase]
          constructor
          · rw [hh] at hx
            rw [Finset.mem_erase] at hx
            exact hx.1
          · rw [hh] at hx
            rw [Finset.mem_erase] at hx
            exact hx.2
      rw [h_filter]
      rw [Finset.sum_singleton]
      exact Finset.card_erase_of_mem v_in_ground

    have sum_part3: ∑ x ∈ (Finset.filter (fun s => s = F.ground) (F.ground.powerset)), x.card = F.ground.card := by
      have h_filter : Finset.filter (λ s => s = F.ground) (F.ground.powerset) = {F.ground} :=
        by
          ext s
          simp
          intro hh
          intro x hx
          rw [hh] at hx
          exact hx
      rw [h_filter]
      rw [Finset.sum_singleton]

    have hcard1: F.ground.card >= 1 := by
        omega

    have sum_part4: (∑ (x ∈ (Finset.filter (fun s => s = F.ground.erase v) (F.ground.erase v).powerset)),
        (if x = F.ground.erase v then ((F.ground.erase v).card + 1) else x.card)) = F.ground.card :=
      by
        have h_filter4 : Finset.filter (fun s => s = F.ground.erase v) (F.ground.erase v).powerset = {F.ground.erase v} :=
          by
            ext s
            simp  [ Finset.subset_iff] --
            intro hh
            intro x hx
            constructor
            · rw [hh] at hx
              rw [Finset.mem_erase] at hx
              exact hx.1
            · rw [hh] at hx
              rw [Finset.mem_erase] at hx
              exact hx.2

        rw [h_filter4]
        rw [Finset.sum_singleton]

        rw [Finset.card_erase_of_mem v_in_ground]
        rw [if_pos]

        rw [Nat.sub_add_cancel hcard1]
        rfl
    rw [hv_equal] at sum_part4

    set termA := ∑ x ∈ Finset.filter (fun s => F.sets s ∧ v ∉ s) (F.ground \ {v}).powerset, x.card
    set termB := (∑ x ∈ Finset.filter (fun s => s = F.ground \ {v}) (F.ground \ {v}).powerset, x.card)
    set termC := (∑ x ∈ Finset.filter (fun s => F.sets s ∧ v ∉ s) (F.ground \ {v}).powerset,
      if x = F.ground \ {v} then (F.ground \ {v}).card + 1 else x.card)
    set termD :=  ∑ x ∈ Finset.filter (fun s => s = F.ground \ {v}) (F.ground \ {v}).powerset,
      if x = F.ground \ {v} then (F.ground \ {v}).card + 1 else x.card
    rw [hv_equal] at sum_part2
    have eq_lem1:termB = F.ground.card - 1:= by
      exact sum_part2
    have eq_lem2: termB + 1 = termD := by
      rw [eq_lem1]
      rw [sum_part4]
      exact Nat.sub_add_cancel hcard1
    rw [sum_part1]
    rw [←eq_lem2]
    rfl

--この部分をメインの証明から分離。分離することでheartbeatsの問題を解決した。
lemma induction_assum_lem (n : Nat) (F: IdealFamily (Fin (n+1))) (idealDelF : IdealFamily (Fin (n+1))) (v : Fin (n+1)) (v_in_ground : v ∈ F.ground) (n_ge_one: n >= 1) (v_notin_minor_ground: v ∉ idealDelF.ground) (ground_ge_two : F.ground.card ≥ 2) (ground_card: F.ground.card = n + 1) (h_ind: P n):
  idealDelF = idealdeletion F v v_in_ground ground_ge_two → (total_size_of_hyperedges  idealDelF.toSetFamily + 1) * 2 ≤
             (number_of_hyperedges idealDelF.toSetFamily) * F.ground.card := by
    intro h
    have h_assum_case: idealDelF.ground.card = n := by
      subst h
      simp [idealdeletion]
      simp_all only [ Finset.card_erase_of_mem, add_tsub_cancel_right]--
    have h_assum_card0: idealDelF.ground.card = F.ground.card -1 := by
      rw [h_assum_case]
      rw [ground_card]
      omega
    have h_assum_card1: idealDelF.ground.card ≥ 1 := by
      omega

    let idealDelFn := @IdealFamily.deletionToN (Fin (n + 1)) n n_ge_one idealDelF v v_notin_minor_ground h_assum_card1
    have minor_ground_card: idealDelFn.ground.card = n := by
      have subs: idealDelFn = @IdealFamily.deletionToN (Fin (n + 1)) n n_ge_one idealDelF v v_notin_minor_ground h_assum_card1 := by
        rfl
      rw [subs]

      have eqset: idealDelFn.ground = Finset.image (finDrop n_ge_one v) idealDelF.ground := by
        rw [subs]
        dsimp [IdealFamily.deletionToN]
      have eqcard: idealDelFn.ground.card = idealDelF.ground.card := by
        rw [eqset]
        --lemma finDropCardEq {n : ℕ} (n_ge_one : n ≥ 1) (v : Fin (n + 1)) (s : Finset (Fin (n+1))) (hvx: v ∉ s)
        exact finDropCardEq n_ge_one v idealDelF.ground v_notin_minor_ground
      rw [eqcard]
      have eqcard2: idealDelF.ground.card = n := by
        subst h
        simp_all only [add_tsub_cancel_right]
      exact eqcard2

    let result := (h_ind.2 idealDelFn) minor_ground_card

    dsimp [normalized_degree_sum] at result
    rw [minor_ground_card] at result
    --deletonToNをしても、total_sizeもnumber_of_hyperedgesも変わらないという定理を最後に適用する必要がある。
    --lemma IdealFamily.deletionToN_number {n : ℕ} (n_ge_one : n ≥ 1) (F : IdealFamily (Fin (n + 1))) (v : Fin (n + 1)) (hvf : v ∉ F.ground)
    --(ground_ge_two : F.ground.card ≥ 1) : number_of_hyperedges (@IdealFamily.deletionToN (Fin n) n n_ge_one F v hvf ground_ge_two).toSetFamily = number_of_hyperedges F.toSetFamily
    have eqcard_number: number_of_hyperedges idealDelF.toSetFamily = number_of_hyperedges idealDelFn.toSetFamily := by
      have minor_ground_card_ge1: idealDelF.ground.card ≥ 1 := by
        subst h
        simp_all only [add_tsub_cancel_right]
      exact Eq.symm (IdealFamily.deletionToN_number n_ge_one idealDelF v v_notin_minor_ground minor_ground_card_ge1)
    have eqcard_total: total_size_of_hyperedges idealDelF.toSetFamily = total_size_of_hyperedges idealDelFn.toSetFamily := by
      exact Eq.symm (deletion_total n idealDelF n_ge_one v v_notin_minor_ground h_assum_card1)
    rw [←eqcard_number] at result
    rw [←eqcard_total] at result

    rw [ground_card]
    rw [h]
    --goal (total_size_of_hyperedges (idealdeletion F v v_in_ground ground_ge_two).toSetFamily + 1) * 2 ≤
    --  number_of_hyperedges (idealdeletion F v v_in_ground ground_ge_two).toSetFamily * (n + 1)
    --ここでheartbeatがかかる。文字を置くとか、補題として分割するとか対処のしようはあるかも。
    have subs2: number_of_hyperedges idealDelF.toSetFamily = number_of_hyperedges (idealdeletion F v v_in_ground ground_ge_two).toSetFamily := by
      rw [h]
    have subs3: total_size_of_hyperedges idealDelF.toSetFamily = total_size_of_hyperedges (idealdeletion F v v_in_ground ground_ge_two).toSetFamily := by
      rw [h]
    simp
    rw [←subs2]
    rw [←subs3]
    --goal (total_size_of_hyperedges idealDelF.toSetFamily + 1) * 2 ≤ number_of_hyperedges idealDelF.toSetFamily * (n + 1)

    have eqlem2: 2 ≤ number_of_hyperedges idealDelF.toSetFamily:= by
      dsimp [number_of_hyperedges]
      exact hyperedges_card_ge_two idealDelF h_assum_card1

    linarith

theorem degonemain (n : Nat) (F : IdealFamily (Fin (n+1))) (v : Fin (n+1)) (v_in_ground : v ∈ F.ground) (singleton_hyperedge_none : ¬ F.sets {v}) (ground_ge_two : F.ground.card ≥ 2) (ground_card: F.ground.card = n + 1) (h_ind: P n): normalized_degree_sum F.toSetFamily ≤ 0 :=
  by

    have degree_one: degree F.toSetFamily v = 1 := by
      exact degree_one_if_not_hyperedge F v_in_ground singleton_hyperedge_none
    --次数1があるということは、vは全体集合のみを含む。
    --goal normalized_degree_sum F.toSetFamily ≤ 0
    rw [normalized_degree_sum]
    by_cases ground_minus_v_none:(F.sets (F.ground \ {v}))
    · case pos =>
      have total := ground_minus_v_ideal_total F v v_in_ground ground_minus_v_none singleton_hyperedge_none ground_ge_two
      have number := ground_minus_v_ideal_number F v v_in_ground ground_minus_v_none singleton_hyperedge_none
      rw [total, number]
      --simp_all only [ Nat.cast_add, Nat.cast_one]
      simp_all --ないとエラー

      have basic_ineq (n : ℕ) (h : 1 ≤ n) : 2^n ≥ n + 1 :=
       by
        induction n with
        | zero =>
          -- 基底ケース: n = 0 は不適
          by_contra _
          simp_all only [nonpos_iff_eq_zero]
          simp_all only [zero_le, add_zero]
        | succ k ih =>
          rw [pow_succ 2 k]
          simp_all --only [le_add_iff_nonneg_left]
          --have _ : k ≥ 0 := Nat.zero_le k

          by_cases h1: k = 0
          · -- k = 0 の場合
            rw [h1]
            simp only [pow_zero, mul_one]
            norm_num
          · -- k ≥ 1 の場合
            have k_ge_1 : k ≥ 1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h1)

            -- 帰納法の仮定を適用
            have ih_applied := ih k_ge_1
            apply  ge_iff_le.mp

            calc
              2 ^ k * 2 = 2 * 2^k := by ring
              _ ≥ 2 * (k + 1) := mul_le_mul_left' ih_applied 2
              _ = k + k + 2 := by ring
              _ ≥ k + 1 + 2 := by
                apply add_le_add_right
                simp_all only [add_le_add_iff_left]
              _ ≥ (k + 1) + 1 := by
                simp only [add_le_add_iff_left, Nat.one_le_ofNat]--

      --以下はゴールと同じ。帰納法で示す必要あり。nがゼロの時はおかしくなるので一つずらしたほうがいいかも。
      --have inequality_calc (n : ℕ) : (n * 2^(n - 1) + (n + 1)) * 2 ≤ (2^n + 1) * (n + 1) := by
      have inequality_calc (n : ℕ) : ((n+1) * (2^n) + (n + 2))* 2 ≤ (2^(n+1) + 1) * (n + 2) := by
        induction n with
        | zero =>
          simp only [ pow_zero, Nat.reduceAdd, Nat.reduceMul, pow_one, le_refl]--

        | succ k ih =>
        -- 帰納段階: n = k + 1 を証明
        -- 目標:((k + 1) * 2^k + (k + 2)) * 2 ≤ (2^(k + 1) + 1) * (k + 2)
          simp_all
          by_cases h1: k = 0
          case pos =>
            rw [h1]
            simp_all only [Nat.one_pow, Nat.one_add]
            subst h1
            simp only [  Nat.reduceAdd]
            simp_all only [Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLeDiff]--
          case neg =>
          --以下はコメントアウトするとエラー
          have hh1: k ≥ 1 := by
            simp_all only [ge_iff_le]
            omega

          calc
              ((k + 2) * 2^(k+1) + (k + 3)) * 2
            = (k + 2) * 2^(k + 2) + 2 * (k + 3) := by ring
         _  = (k + 2) * 2^(k + 2) + 2 * (k + 3) + (2 ^ (k+2)-(k+3)) - (2^(k+2) - (k+3))   := by simp_all only [true_implies, ge_iff_le, le_add_iff_nonneg_left, zero_le, add_tsub_cancel_right]
         _  = (2^(k + 2) + 1) * (k + 3) - (2^(k+2) - (k+2)-1) := by
               rw [ineq_lem (k+1)]
               simp_all only [ ge_iff_le,  zero_le]
               rfl
         _  ≤ (2^(k + 2) + 1) * (k + 3) := by
                simp_all only [ ge_iff_le]
                omega
      --goal (↑(F.ground.card - 1) * 2 ^ (F.ground.card - 2) + ↑F.ground.card) * 2 ≤ (2 ^ (F.ground.card - 1) + 1) * ↑F.ground.card

      let result :=  inequality_calc (n-1)
      norm_cast at result
      norm_cast
      rw [Nat.sub_add_cancel ground_ge_two] at result
      have n_eq: n - 1 + 2 = n + 1 := by
        omega
      rw [n_eq] at result
      exact result
      --by_cases ground_minus_v_none:(F.sets (F.ground \ {v}))のcase posの場合の証明おわり

    · case neg => --by_cases ground_minus_v_none:(F.sets (F.ground \ {v}))のcase negの場合の証明
      --idealDelFとFでnumber_of_hyperedgesが同じになることを示す。
      --idealDelFとFでtotal_size_of_hyperedgesが1つちがいになることを示す。
      --idealDefFのnormalized_degree_sumが非負のとき、Fも非負であることを示す。

      let idealDelF := idealdeletion F v v_in_ground ground_ge_two

      have v_notin_minor_ground: v ∉ idealDelF.ground := by
        intro h
        dsimp [idealDelF] at h
        rw [idealdeletion] at h
        simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false]--

      --このあとの補題のomegaの計算に利用されているよう。
      have minor_ground_card: idealDelF.ground.card = n := by
        simp_all only [idealDelF]
        --goal ((F.toSetFamily ∖ v) v_in_ground ground_ge_two).ground.card = n
        dsimp [idealdeletion]
        simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]--

      dsimp [P] at h_ind
      have n_ge_one : n ≥ 1 := by
        omega
      /-
      have minor_ground_card_ge_one: idealDelF.ground.card ≥ 1 := by
        simp_all only [ idealDelF]
        omega
      let idealDelF' := @IdealFamily.deletionToN (Fin (n + 1)) n n_ge_one idealDelF v v_notin_minor_ground minor_ground_card_ge_one

      let ineq := h_ind.2 idealDelF' (by
        simp_all only [ge_iff_le]
        dsimp [idealDelF']
        dsimp [IdealFamily.deletionToN]
        dsimp [idealDelF]

        calc
          (Finset.image (finDrop n_ge_one v) (idealdeletion F v v_in_ground ground_ge_two).ground).card
        = ((idealdeletion F v v_in_ground ground_ge_two).ground).card := by
            exact finDropCardEq n_ge_one v (idealdeletion F v v_in_ground ground_ge_two).ground v_notin_minor_ground
      _ = n := by
            simp_all only [ge_iff_le]
      )

      --rw [normalized_degree_sum] at ineq
      --simp only [ Nat.cast_add, Nat.cast_one] at ineq
      --Fin nとFin n+1の変換にIdealFamily.deletionToN_numberは必要かも。不等式系はFin n+1の世界にそろえればいいか。
      --dsimp [idealDelF'] at ineq

      --#check IdealFamily.deletionToN_number n_ge_one idealDelF v v_notin_minor_ground minor_ground_card_ge_one
      --simp [IdealFamily.deletionToN_number n_ge_one idealDelF v v_notin_minor_ground minor_ground_card_ge_one] at ineq
      --ineqの方の変数と、ゴールの方の変数が同じものを指すものがあるので、それを補題として示す。
      -/

      let domain := Finset.filter (λ (s:Finset (Fin (n+1))) => F.sets s) (F.ground.powerset)
      let range := Finset.filter (λ (s:Finset (Fin (n+1))) => (F.sets s ∧ v ∉ s) ∨ s = F.ground.erase v) ((F.ground.erase v).powerset)

      set i := (λ (s : Finset (Fin (n+1))) (_: s ∈ domain) => s.erase v)
        --v notin sの場合はそのままで、v in sの場合はs erase vとなる。
      have hi : ∀ (s : Finset (Fin (n+1))), (hs: s ∈ domain) → (i s hs) ∈ range:= by
        intro s hs'
        dsimp [i,range]
        rw [Finset.mem_filter]
        rw [Finset.mem_powerset]
        --goal s.erase v ⊆ F.ground.erase v ∧ (F.sets (s.erase v) ∧ v ∉ s.erase v ∨ s.erase v = F.ground.erase v)
        constructor
        · --goal s.erase v ⊆ F.ground.erase v  .. この分解はおかしくないか？orが消えている。
          simp only [Finset.mem_filter, Finset.mem_powerset, domain] at hs'
          obtain ⟨left, _⟩ := hs'
          intro x hx
          simp only [Finset.mem_erase,ne_eq, not_false_eq_true, true_and] at hx
          obtain ⟨_, right_1⟩ := hx
          simp only [Finset.mem_erase]
          constructor
          · simp only [ne_eq]
            simp_all only [not_false_eq_true]
          · apply left
            simp_all only

        · --goal F.sets (s.erase v) ∧ v ∉ s.erase v ∨ s.erase v = F.ground.erase v
          --constructor --このconstructorはいらない。orが消える。
          dsimp [domain] at hs'
          rw [Finset.mem_filter] at hs'
          rw [Finset.mem_powerset] at hs'
          --singleton_hyperedge_noneからhyperedgeでvを含んでいるものは、全体集合のみ。
          by_cases s=F.ground
          · case pos =>
              dsimp [i,range]
              rename_i h
              subst h
              simp only [or_true]

          · case neg h_neg =>
              have vnotin: v ∉ s := by
                by_contra h_contra
                have v_subset_s: {v} ⊆ s := by
                  --simp_all only [ge_iff_le]
                  rw [Finset.singleton_subset_iff]
                  exact h_contra
                have v_hyperedge: F.sets {v} := by
                  exact F.down_closed {v} s hs'.2 h_neg v_subset_s
                contradiction
              simp only [Finset.mem_erase, ne_eq]
              left
              constructor
              · simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem]
              · simp_all only [ not_true_eq_false, and_self, not_false_eq_true]

      have i_inj   (s : Finset (Fin (n+1))) (hs : s ∈ domain) (t : Finset (Fin (n+1))) (ht : t ∈ domain) : s.erase v = t.erase v → s = t:= by
        intro h_inj
        --sがvを含むかで場合分け。
        by_cases hv_in_s: v ∈ s
        · case pos =>
          by_cases hv_in_t: v ∈ t
          · case pos =>
            ext a
            apply Iff.intro
            · intro h
              by_cases hav: a = v
              case pos =>
                rw [hav]
                exact hv_in_t
              case neg =>
                have asr: a ∈ s.erase v := by
                  rw [Finset.mem_erase]
                  constructor
                  exact hav
                  exact h
                have atr: a ∈ t.erase v := by
                  rw [←h_inj]
                  exact asr
                simp_all-- only [Finset.mem_erase]
            · intro h
              by_cases hav: a = v
              case pos =>
                rw [hav]
                exact hv_in_s
              case neg =>
                have atr: a ∈ t.erase v := by
                  rw [Finset.mem_erase]
                  constructor
                  exact hav
                  exact h
                have asr: a ∈ s.erase v := by
                  rw [h_inj]
                  exact atr
                rw [Finset.mem_erase] at asr
                simp_all only [and_self]

          · case neg =>
            --v in sということはsは全体集合であり、ground - vはground_minus_v_none : ¬F.sets (F.ground \ {v})の仮定よりhyperedgeではない。よって、h_inkに矛盾。
            have neg_lem: s = F.ground := by
              --singleton_hyperedge_none : ¬F.sets {v}から言える。
              by_contra h_contra
              have v_subset_s: {v} ⊆ s := by
                rw [Finset.singleton_subset_iff]
                exact hv_in_s
              have v_hyperedge: F.sets {v} := by
                dsimp [domain] at hs
                rw [Finset.mem_filter] at hs
                rw [Finset.mem_powerset] at hs
                exact F.down_closed {v} s hs.2 h_contra v_subset_s
              contradiction
            --s.erase v = t.erase vより、tは、groundかground-vである。
            have t_lem: t = F.ground ∨ t = F.ground.erase v := by
              subst neg_lem
              simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem, or_true]--

            cases t_lem with
            | inl h1 =>
              subst h1 neg_lem
              simp
            | inr h2 =>
              --仮定htに矛盾
              rw [h2] at ht
              have : ¬F.sets (F.ground.erase v) := by
                convert ground_minus_v_none
                exact Finset.erase_eq F.ground v
              dsimp [domain] at ht
              rw [Finset.mem_filter] at ht
              rw [Finset.mem_powerset] at ht
              let ht2 := ht.2
              contradiction

        · case neg => -- v ∉ sの場合
          by_cases hv_in_t: v ∈ t
          · case pos =>
            --v notin sということはsは全体集合であり、ground - vはground_minus_v_none : ¬F.sets (F.ground \ {v})の仮定よりhyperedgeではない。よって、h_inkに矛盾。
            have neg_lem: t = F.ground := by
              --singleton_hyperedge_none : ¬F.sets {v}から言える。
              by_contra h_contra
              have v_subset_t: {v} ⊆ t := by
                rw [Finset.singleton_subset_iff]
                exact hv_in_t
              have v_hyperedge: F.sets {v} := by
                dsimp [domain] at ht
                rw [Finset.mem_filter] at ht
                rw [Finset.mem_powerset] at ht
                exact F.down_closed {v} t ht.2 h_contra v_subset_t
              contradiction
            have s_lem: s = F.ground ∨ s = F.ground.erase v := by
              subst neg_lem
              simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem, or_true]--
            cases s_lem with
            | inl h1 =>
              subst h1 neg_lem
              simp_all only [ not_true_eq_false]
            | inr h2 =>
              rw [h2] at hs
              have : ¬F.sets (F.ground.erase v) := by
                convert ground_minus_v_none
                exact Finset.erase_eq F.ground v
              subst neg_lem h2
              simp_all only [Finset.mem_filter,  and_false,  domain]--

          · case neg =>
            simp_all only [ not_false_eq_true, Finset.erase_eq_of_not_mem]


      have i_surj : ∀ (ss:Finset (Fin (n+1))), ss ∈ range → ∃ (s:Finset (Fin (n+1))), ∃ (hs : s ∈ domain), i s hs = ss := by
        intro ss hss
        have hv_notin_is: v ∉ ss:= by
          simp only [Finset.mem_filter, range] at hss
          obtain ⟨_, right⟩ := hss
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [not_true_eq_false,and_false, false_or, Finset.mem_erase, ne_eq]--

        by_cases hvs: v ∈ ss
        · case pos =>
          use F.ground
          have s_eq: ss = F.ground := by
            simp_all only [not_true_eq_false]
          subst s_eq
          simp_all only [ not_true_eq_false]
        · case neg =>
          rw [Finset.mem_filter] at hss
          rw [Finset.mem_powerset] at hss
          simp_all only [i]
          obtain ⟨left, right⟩ := hss
          cases right with
          | inl h =>
            use ss
            simp_all only [Finset.mem_filter, not_false_eq_true,Finset.erase_eq_of_not_mem, domain]--
            simp --これがないとエラー
            rw [Finset.subset_erase] at left
            exact left.1

          | inr h_1 =>
            use F.ground
            rw [h_1]
            simp
            dsimp [domain]
            rw [Finset.mem_filter]
            constructor
            subst h_1
            simp only [Finset.mem_powerset,subset_refl]--
            exact F.has_ground


      have number_eq: number_of_hyperedges F.toSetFamily = number_of_hyperedges idealDelF.toSetFamily := by
        dsimp [number_of_hyperedges,idealDelF]
        rw [idealdeletion]
        simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]
        --goal: (Finset.filter F.sets F.ground.powerset).card =
        --(Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground.erase v) (F.ground.erase v).powerset).card

        have bij := Finset.card_bij i hi i_inj i_surj  --idealSumを参考にするとdomainとrangeを設定したほうがいい。その間のbijectionを証明。
        simp_all only [range]
        congr

      have hv_equal: F.ground.erase v = F.ground \ {v} := by
        exact Finset.erase_eq F.ground v

      have total_eq: total_size_of_hyperedges F.toSetFamily = total_size_of_hyperedges idealDelF.toSetFamily + 1:= by
        --rw [Ideal.total_degone_card F.toSetFamily v v_in_ground degree_one F.has_ground ground_ge_two]
        dsimp [total_size_of_hyperedges]
        dsimp [idealDelF]
        dsimp [idealdeletion]
        simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]

        let ff := λ (s:Finset (Fin (n+1))) => s.card
        let gg := λ (s:Finset (Fin (n+1))) => if s = F.ground.erase v then s.card + 1 else s.card

        have comm: ∀ (s:Finset (Fin (n+1))), (sd: s ∈ domain) → ff s = gg (i s sd) := by
          intro s hs
          by_cases h: s = F.ground
          · case pos =>
            dsimp [i,ff,gg]
            rw [h]
            simp
            rw [Finset.card_erase_of_mem v_in_ground]
            omega

          · case neg => --h: not (s = F.ground)
            dsimp [i,ff,gg]
            dsimp [domain] at hs
            rw [Finset.mem_filter] at hs
            rw [Finset.mem_powerset] at hs
            obtain ⟨_, right⟩ := hs
            have vns: v ∉ s := by
              by_contra h_contra
              exact h ((degree_one_ground F v v_in_ground ground_ge_two degree_one s right) h_contra)

            --#check hyperedges_not_through_v F.toSetFamily v v_in_ground degree_one F.has_ground s right hはv notin s
            --goal s.card = if s.erase v = F.ground.erase v then (s.erase v).card + 1 else (s.erase v).card
            have tmp_lem: s.erase v = s:= by
               exact Finset.erase_eq_of_not_mem vns

            by_cases not_lem2: s = F.ground.erase v
            · case pos =>
              rw [not_lem2]
              simp
              rw [not_lem2] at right

              rw [hv_equal] at right
              exact ground_minus_v_none right
            · case neg =>
              rw [tmp_lem]
              rw [if_neg not_lem2]

        --goal (Finset.filter (fun s => F.sets s ∧ v ∉ s) F.ground.powerset).sum Finset.card + (n + 1) =
        --(Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground.erase v) (F.ground.erase v).powerset).sum Finset.card + 1
        let sumcard := Finset.sum_bij i hi i_inj i_surj comm
        dsimp [domain,range,ff,gg] at sumcard

        convert sumcard

        clear i hi i_inj i_surj comm sumcard

        exact total_eq_lem n F v v_in_ground ground_minus_v_none ground_ge_two ground_card h_ind

      rw [number_eq]
      rw [total_eq]

      let induction_assum := induction_assum_lem n F idealDelF v v_in_ground n_ge_one v_notin_minor_ground ground_ge_two ground_card h_ind

      rw [ground_card] at induction_assum ⊢
      ring_nf
      ring_nf at induction_assum
      simp at induction_assum
      simp
      linarith

end Ideal
