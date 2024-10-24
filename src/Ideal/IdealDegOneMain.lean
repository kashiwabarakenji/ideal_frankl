import Mathlib.Data.Finset.Basic --hiding eq_empty_of_subset_empty
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import Ideal.IdealSum
import Ideal.IdealNumbers
import Ideal.IdealSimple
import Ideal.IdealDegreeOne
import Ideal.IdealFin
import LeanCopilot


set_option maxHeartbeats 500000

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α]

lemma example_ineq (k : ℕ) :
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
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le]


          rw [pow_succ 2 k]

          by_cases h1: k = 0
          case pos =>
            rw [h1]
            simp_all only [Nat.one_pow, Nat.one_add]
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
               simp_all only [ge_iff_le, true_implies, le_add_iff_nonneg_left, zero_le, Nat.ofNat_pos, mul_le_mul_left,
               Nat.reduceAdd, add_left_inj]
               omega
             _ ≥ k + 2  := by
                simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
                omega
          simp_all only [ge_iff_le, true_implies, le_add_iff_nonneg_left, zero_le, Nat.ofNat_pos, mul_le_mul_left]
          omega
    have hh1: k + 1 ≥ 1 := by
      simp_all only [ge_iff_le]
      omega

    have add_sub_assoc (nn mm kk : ℕ) (h : mm ≥ kk) : nn + (mm - kk) = (nn + mm) - kk :=
      by
        rw [←Nat.add_sub_cancel' h]
        simp_all only [ge_iff_le, add_tsub_cancel_of_le]
        omega

    calc
    (k + 1) * 2^(k + 1) + 2 * (k + 2) + (2 ^ (k + 1) - (k + 2))
      = 2^(k + 1) * (k + 1) + 2 * (k + 2) + (2 ^ (k + 1) - (k + 2)) := by ring_nf
    _ = (2^(k + 1) * (k + 1) + 2*k + 4) + (2 ^ (k + 1) - (k + 2)) := by ring_nf
    _ = ((2^(k + 1) * (k + 1) + 2*k + 4) + 2 ^ (k + 1)) - (k + 2) := by
      --#check add_sub_assoc (2^(k + 1) * (k + 1) + 2*k + 4) (2 ^ (k + 1)) (k + 2) (basic_ineq (k+1) hh1)
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

theorem degonemain (n : Nat) (F : IdealFamily (Fin (n+1))) (v : Fin (n+1)) (hv_left : v ∈ F.ground) (hv_singleton : ¬ F.sets {v}) (hcard0 : F.ground.card ≥ 2) (hcard: F.ground.card = n + 1) (h_ind: P n): normalized_degree_sum F.toSetFamily ≤ 0 :=
  by

    have degree_one: degree F.toSetFamily v = 1 := by
      exact degree_one_if_not_hyperedge F hv_left hv_singleton
    --次数1があったからといって、normalized_degree_sumが負になるとはすぐに言えない。ただし、次数1があるということは、vは全体集合のみを含む。
    --goal normalized_degree_sum F.toSetFamily ≤ 0
    rw [normalized_degree_sum]
    by_cases hv_hyperedge:(F.sets (F.ground \ {v}))
    · case pos =>
      have total := ground_minus_v_ideal_total F v hv_left hv_hyperedge hv_singleton hcard0
      have number := ground_minus_v_ideal_number F v hv_left hv_hyperedge hv_singleton
      rw [total, number]
      simp_all only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one]
      simp_all

      have basic_ineq (n : ℕ) (h : 1 ≤ n) : 2^n≥n+1 :=
        by
          induction n with
          | zero =>
            -- 基底ケース: n = 0 は不適
            by_contra _
            simp_all only [nonpos_iff_eq_zero, one_ne_zero]

          | succ k ih =>
          have k_geq_1 : k ≥ 0 := by
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le]

          rw [pow_succ 2 k]

          by_cases h1: k = 0
          case pos =>
            rw [h1]
            simp_all only [Nat.one_pow, Nat.one_add]
            omega
          case neg =>
          have hh1: k ≥ 1 := by
            simp_all only [ge_iff_le]
            omega
              -- 2^(k + 1) = 2 * 2^k
          have : 2 * 2^k ≥ 2 * (k + 1) := mul_le_mul_of_nonneg_left (ih hh1) (by norm_num)

          -- 2 * (k + 1) = k + 1 + k + 1 = 2k + 2 ≥ k + 2  これは k ≥ 0 で常に成り立つ
          have : 2 * (k + 1) ≥ k + 2 := by
           calc
             2 * (k + 1) = k + 1 + k + 1 := by ring
             _ = (k + k) + (1 + 1) := by
               simp_all only [ge_iff_le, true_implies, le_add_iff_nonneg_left, zero_le, Nat.ofNat_pos, mul_le_mul_left,
               Nat.reduceAdd, add_left_inj]
               omega
             _ ≥ k + 2  := by
                simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
                omega
          simp_all only [ge_iff_le, true_implies, le_add_iff_nonneg_left, zero_le, Nat.ofNat_pos, mul_le_mul_left]
          omega

      --以下はゴールと同じ。帰納法で示す必要あり。nがゼロの時はおかしくなるので一つずらしたほうがいいかも。
      --have inequality_example (n : ℕ) : (n * 2^(n - 1) + (n + 1)) * 2 ≤ (2^n + 1) * (n + 1) := by
      have inequality_example (n : ℕ) : ((n+1) * (2^n) + (n + 2))* 2 ≤ (2^(n+1) + 1) * (n + 2) := by
        induction n with
        | zero =>
          simp_all only [ge_iff_le, zero_add, pow_zero, mul_one, Nat.reduceAdd, Nat.reduceMul, pow_one, le_refl]

        | succ k ih =>
        -- 帰納段階: n = k + 1 を証明
        -- 目標:((k + 1) * 2^k + (k + 2)) * 2 ≤ (2^(k + 1) + 1) * (k + 2)
          simp_all
          by_cases h1: k = 0
          case pos =>
            rw [h1]
            simp_all only [Nat.one_pow, Nat.one_add]
            subst h1
            simp_all only [nonpos_iff_eq_zero, one_ne_zero, zero_le, tsub_eq_zero_of_le, pow_zero, mul_one, zero_add,
              one_mul, Nat.reduceAdd, le_refl, false_implies, Nat.reduceMul, pow_one]
            simp_all only [Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLeDiff]
          case neg =>
          --以下はコメントアウトするとエラー
          have hh1: k ≥ 1 := by
            simp_all only [ge_iff_le]
            omega

          calc  --1ずらす必要あり。

              ((k + 2) * 2^(k+1) + (k + 3)) * 2
            = (k + 2) * 2^(k + 2) + 2 * (k + 3) := by ring
         _  = (k + 2) * 2^(k + 2) + 2 * (k + 3) + (2 ^ (k+2)-(k+3)) - (2^(k+2) - (k+3))   := by simp_all only [true_implies, ge_iff_le, le_add_iff_nonneg_left, zero_le, add_tsub_cancel_right]
         _  = (2^(k + 2) + 1) * (k + 3) - (2^(k+2) - (k+2)-1) := by
               rw [example_ineq (k+1)]
               simp_all only [true_implies, ge_iff_le, le_add_iff_nonneg_left, zero_le]
               rfl
         _  ≤ (2^(k + 2) + 1) * (k + 3) := by
                simp_all only [true_implies, ge_iff_le, le_add_iff_nonneg_left, zero_le]
                omega
      --goal (↑(F.ground.card - 1) * 2 ^ (F.ground.card - 2) + ↑F.ground.card) * 2 ≤ (2 ^ (F.ground.card - 1) + 1) * ↑F.ground.card




      let result :=  inequality_example (n-1)
      norm_cast at result
      norm_cast
      rw [Nat.sub_add_cancel hcard0] at result
      have n_eq: n - 1 + 2 = n + 1 := by
        omega
      rw [n_eq] at result
      exact result



      --by_cases hv_hyperedge:(F.sets (F.ground \ {v}))のcase posの場合の証明おわり

    · case neg => --by_cases hv_hyperedge:(F.sets (F.ground \ {v}))のcase negの場合の証明
      --idealDelFとFでnumber_of_hyperedgesが同じになることを示す。
      --idealDelFとFでtotal_size_of_hyperedgesが1つちがいになることを示す。
      --idealDefFのnormalized_degree_sumが非負のとき、Fも非負であることを示す。
      simp only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one] at hv_singleton degree_one ⊢
      --lemma total_degone_card {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground)(gcard: F.ground.card ≥ 2) :
      --total_size_of_hyperedges F = (F.ground.powerset.filter (λ s => F.sets s ∧ v ∉ s )).sum Finset.card + F.ground.card
      --rw [Ideal.total_degone_card F.toSetFamily v hv_left degree_one F.univ_mem hcard0]
      --rw [Ideal.erase_ground_card F.toSetFamily v hv_left degree_one]

      let idealDelF := IdealDeletion.idealdeletion F v hv_left hcard0
      --delFじゃなくidealFに統一する。

      have hvfideal: v ∉ idealDelF.ground := by
        intro h
        --simp_all only [ge_iff_le]
        dsimp [idealDelF] at h
        rw [IdealDeletion.idealdeletion] at h
        simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true]

      have hcard1ideal: idealDelF.ground.card = n := by
        --simp_all only [ge_iff_le]
        simp_all only [idealDelF]
        --goal ((F.toSetFamily ∖ v) hv_left hcard0).ground.card = n
        dsimp [IdealDeletion.idealdeletion]
        simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]


      have hcard2ideal: idealDelF.ground.card ≥ 1 := by
        simp_all only [ge_iff_le, idealDelF]
        omega

      dsimp [P] at h_ind
      --#check h_ind
      have nposi : n ≥ 1 := by
        omega
      let idealDelF' := @IdealFamily.deletionToN (Fin (n + 1)) n nposi idealDelF v hvfideal hcard2ideal
      let ineq := h_ind.2 idealDelF' (by
        simp_all only [ge_iff_le]
        dsimp [idealDelF']
        dsimp [IdealFamily.deletionToN]
        dsimp [idealDelF]
        --simp_all only [ge_iff_le]
        --#check finDropCardEq nposi v (IdealDeletion.idealdeletion F v hv_left hcard0).ground hvf
        --Ideal.finDropCardEq {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (s : Finset (Fin (n + 1))) (hvx : v ∉ s) :
        -- (Finset.image (finDrop nposi v) s).card = s.card - 1
        calc
          (Finset.image (finDrop nposi v) (IdealDeletion.idealdeletion F v hv_left hcard0).ground).card
        = ((IdealDeletion.idealdeletion F v hv_left hcard0).ground).card := by
            exact finDropCardEq nposi v (IdealDeletion.idealdeletion F v hv_left hcard0).ground hvfideal
      _ = n := by
            simp_all only [ge_iff_le]
      )
      rw [normalized_degree_sum] at ineq
      simp only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one] at ineq
      --rw [Ideal.total_degone_card] at ineq
      --Fin nとFin n+1の変換にIdealFamily.deletionToN_numberは必要かも。不等式系はFin n+1の世界にそろえればいいか。
      dsimp [idealDelF'] at ineq
      --#check IdealFamily.deletionToN_number nposi idealDelF v hvfideal hcard2ideal
      simp [IdealFamily.deletionToN_number nposi idealDelF v hvfideal hcard2ideal] at ineq
      --ineqの方の変数と、ゴールの方の変数が同じものを指すものがあるので、それを補題として示す。
      --集合族のレベルでなく数のレベルで示すとなると、また全単車を構成する必要がある。既存の定理が利用できないか。
      --以下は言明が間違っているかも。証明にはsum_bijを利用するかも。

      let domain := Finset.filter (λ (s:Finset (Fin (n+1))) => F.sets s) (F.ground.powerset)
      let range := Finset.filter (λ (s:Finset (Fin (n+1))) => (F.sets s ∧ v ∉ s) ∨ s = F.ground.erase v) ((F.ground.erase v).powerset)

        --#check Finset.card_bij
        --Finset.card_bij.{u_1, u_2} {α : Type u_1} {β : Type u_2} {s : Finset α} {t : Finset β} (i : (a : α) → a ∈ s → β)
        --(hi : ∀ (a : α) (ha : a ∈ s), i a ha ∈ t)
        --(i_inj : ∀ (a₁ : α) (ha₁ : a₁ ∈ s) (a₂ : α) (ha₂ : a₂ ∈ s), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
        --(i_surj : ∀ b ∈ t, ∃ a, ∃ (ha : a ∈ s), i a ha = b) : s.card = t.card
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
          simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, idealDelF, domain, i]
          obtain ⟨left, _⟩ := hs'
          intro x hx
          simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
          obtain ⟨_, right_1⟩ := hx
          exact left right_1

        · --goal F.sets (s.erase v) ∧ v ∉ s.erase v ∨ s.erase v = F.ground.erase v
          --constructor --このconstructorはいらない。orが消える。
          dsimp [domain] at hs'
          rw [Finset.mem_filter] at hs'
          rw [Finset.mem_powerset] at hs'
          --hv_singletonからhyperedgeでvを含んでいるものは、全体集合のみ。
          by_cases s=F.ground
          · case pos => --rangeのまたはの条件はどこにいったのか。
              dsimp [i,range]
              rename_i h
              subst h
              simp_all only [ge_iff_le, subset_refl, true_and, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
                not_false_eq_true, idealDelF, domain, i]
              simp_all only [or_true]

          · case neg h_neg =>
              have vnotin: v ∉ s := by
                by_contra h_contra
                have v_subset_s: {v} ⊆ s := by
                  simp_all only [ge_iff_le]
                  rw [Finset.singleton_subset_iff]
                  exact h_contra
                have v_hyperedge: F.sets {v} := by
                  exact F.down_closed {v} s hs'.2 h_neg v_subset_s
                contradiction
              simp_all only [ge_iff_le, Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
              simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem, not_true_eq_false, and_self, idealDelF]
              simp_all only [true_or]

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
              simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, idealDelF, domain, i, hi]
              --obtain ⟨left, right⟩ := hs
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
                simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
            · intro h
              simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, idealDelF, domain, i, hi]
              --obtain ⟨left, right⟩ := hs
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
                --simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
                  --have hsv: a ∈ s := by
                rw [Finset.mem_erase] at asr
                simp_all only [not_false_eq_true, Finset.mem_erase, ne_eq, and_self]

          · case neg =>
            --v in sということはsは全体集合であり、ground - vはhv_hyperedge : ¬F.sets (F.ground \ {v})の仮定よりhyperedgeではない。よって、h_inkに矛盾。
            have neg_lem: s = F.ground := by
              --hv_singleton : ¬F.sets {v}から言える。
              by_contra h_contra
              have v_subset_s: {v} ⊆ s := by
                simp_all only [ge_iff_le]
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
              simp_all only [ge_iff_le, not_false_eq_true, Finset.erase_eq_of_not_mem, or_true, idealDelF,
                  i, hi]
                  --t_lemの証明おわり
            cases t_lem with
            | inl h1 =>
              subst h1 neg_lem
              simp_all only [ge_iff_le, not_true_eq_false, idealDelF, i, hi]
            | inr h2 =>
              --仮定htに矛盾
              rw [h2] at ht
              have : ¬F.sets (F.ground.erase v) := by
                convert hv_hyperedge
                exact Finset.erase_eq F.ground v
              dsimp [domain] at ht
              rw [Finset.mem_filter] at ht
              rw [Finset.mem_powerset] at ht
              let ht2 := ht.2
              contradiction

        · case neg => -- v ∉ sの場合
          by_cases hv_in_t: v ∈ t
          · case pos =>
            --v notin sということはsは全体集合であり、ground - vはhv_hyperedge : ¬F.sets (F.ground \ {v})の仮定よりhyperedgeではない。よって、h_inkに矛盾。
            have neg_lem: t = F.ground := by
              --hv_singleton : ¬F.sets {v}から言える。
              by_contra h_contra
              have v_subset_t: {v} ⊆ t := by
                simp_all only [ge_iff_le]
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
              simp_all only [ge_iff_le, not_false_eq_true, Finset.erase_eq_of_not_mem, or_true, idealDelF, i, hi]
            cases s_lem with
            | inl h1 =>
              subst h1 neg_lem
              simp_all only [ge_iff_le, not_true_eq_false, idealDelF, i, hi]
            | inr h2 =>
              rw [h2] at hs
              have : ¬F.sets (F.ground.erase v) := by
                convert hv_hyperedge
                exact Finset.erase_eq F.ground v
              subst neg_lem h2
              simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, and_false, idealDelF, domain,i, hi]

          · case neg =>
            simp_all only [ge_iff_le, not_false_eq_true, Finset.erase_eq_of_not_mem, idealDelF, i, hi]

        --示すものが違う気がする。
      have i_surj : ∀ (ss:Finset (Fin (n+1))), ss ∈ range → ∃ (s:Finset (Fin (n+1))), ∃ (hs : s ∈ domain), i s hs = ss := by
        intro ss hss
        have hv_notin_is: v ∉ ss:= by
          simp_all only [ge_iff_le]
          dsimp [i]
          simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, ne_eq, not_true_eq_false,
            false_and, not_false_eq_true, and_true, idealDelF, i]
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl, Finset.singleton_subset_iff,
            Finset.sdiff_subset, domain, range]
          obtain ⟨_, right⟩ := hss
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [subset_refl, Finset.singleton_subset_iff, Finset.sdiff_subset, not_true_eq_false,
            and_false, false_or, Finset.mem_erase, ne_eq, and_true]

        by_cases hvs: v ∈ ss
        · case pos =>
          use F.ground
          have s_eq: ss = F.ground := by
            simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, not_false_eq_true, and_true, not_true_eq_false,
  idealDelF, i, hi]
          subst s_eq
          simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, not_false_eq_true, and_true, not_true_eq_false]
        · case neg =>
          rw [Finset.mem_filter] at hss
          rw [Finset.mem_powerset] at hss
          simp_all only [ge_iff_le, not_false_eq_true, and_true, Finset.erase_eq_of_not_mem, idealDelF, i, hi]
          --have hsscopy := ss ∈ domain
          obtain ⟨left, right⟩ := hss
          cases right with
          | inl h =>
            --have ssh: i ss hsscopy = ss
            use ss
            simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl, not_false_eq_true,
              Finset.erase_eq_of_not_mem, domain]
            simp
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
            simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl, Finset.mem_erase, ne_eq,
              not_true_eq_false, and_true, not_false_eq_true, domain]
            exact F.univ_mem


      have number_eq: number_of_hyperedges F.toSetFamily = number_of_hyperedges idealDelF.toSetFamily := by
        dsimp [number_of_hyperedges,idealDelF]
        rw [IdealDeletion.idealdeletion]
        simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]
        --goal: (Finset.filter F.sets F.ground.powerset).card =
        --(Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground.erase v) (F.ground.erase v).powerset).card

        have bij := Finset.card_bij i hi i_inj i_surj  --idealSumを参考にするとdomainとrangeを設定したほうがいい。その間のbijectionを証明。
        --dsimp [domain, range] at bij
        simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, Finset.mem_erase, ne_eq, not_true_eq_false,
          false_and, not_false_eq_true, and_true, and_imp, subset_refl, exists_prop, Finset.singleton_subset_iff,
          Finset.sdiff_subset, idealDelF, domain, i, range]
        congr

      have hv_equal: F.ground.erase v = F.ground \ {v} := by
        exact Finset.erase_eq F.ground v

      --示すべきものが違う可能性。number_of_hyperedgesのほうはdeletionToNを使ってなかった。
      /-have total_eq: total_size_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi idealDelF v hvfideal hcard2ideal).toSetFamily = (Finset.filter (fun s => v ∉ s ∧ F.sets s) F.ground.powerset).sum Finset.card := by
        simp_all only [ge_iff_le]
        --simp_all only [IdealFamily.deletionToN]
        rw [deletion_total]
        dsimp [idealDelF]
        dsimp [total_size_of_hyperedges]
        dsimp [IdealDeletion.idealdeletion]
        -/
      --degree F.toSetFamily v=1の場合。一般論から言えないか。
      --lemma ideal_and_deletion {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2) (hx_hyperedge_not : ¬ F.sets (F.ground \ {x})) :
      --total_size_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily = total_size_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard) + (F.ground.card - 1
      --は使える可能性。全体集合がなくなった分が調整されている。
      --次が一般の場合だが、contractionが関係してくるので、一般の場合に帰着するよりも直接証明したほうがいいかも。
      --theorem hyperedge_totalsize_deletion_contraction_have_z {α : Type} [DecidableEq α] [Fintype α]
      -- degree oneのほうが関係してくるかも。
      -- lemma total_degone_card {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground)(gcard: F.ground.card ≥ 2) :
      -- total_size_of_hyperedges F = (F.ground.powerset.filter (λ s => F.sets s ∧ v ∉ s )).sum Finset.card + F.ground.card

      have total_eq: total_size_of_hyperedges F.toSetFamily = total_size_of_hyperedges idealDelF.toSetFamily + 1:= by
        --rw [Ideal.total_degone_card F.toSetFamily v hv_left degree_one F.univ_mem hcard0]
        dsimp [total_size_of_hyperedges]
        dsimp [idealDelF]
        dsimp [IdealDeletion.idealdeletion] --分解されすぎるかも。
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
            rw [Finset.card_erase_of_mem hv_left]
            omega

          · case neg => --h: not (s = F.ground)
            dsimp [i,ff,gg]
            dsimp [domain] at hs
            rw [Finset.mem_filter] at hs
            rw [Finset.mem_powerset] at hs
            obtain ⟨left, right⟩ := hs
            have vns: v ∉ s := by
              simp_all only [ge_iff_le]
              by_contra h_contra
              exact h ((degree_one_ground F v hv_left hcard0 degree_one s right) h_contra)

            --#check hyperedges_not_through_v F.toSetFamily v hv_left degree_one F.univ_mem s right hはv notin s
            --goal s.card = if s.erase v = F.ground.erase v then (s.erase v).card + 1 else (s.erase v).card
            --s.erase v = F.ground.erase vを満たさないことを示したい。
            --使う仮定。degree v = 1。
            have tmp_lem: s.erase v = s:= by
               exact Finset.erase_eq_of_not_mem vns

            by_cases not_lem2: s = F.ground.erase v
            · case pos =>
              rw [not_lem2]
              simp
              rw [not_lem2] at right

              have eq_lem: F.ground.erase v = F.ground \ {v} := by
                exact Finset.erase_eq F.ground v

              rw [eq_lem] at right
              exact hv_hyperedge right
            · case neg =>
              rw [tmp_lem]
              rw [if_neg not_lem2]

        --goal (Finset.filter (fun s => F.sets s ∧ v ∉ s) F.ground.powerset).sum Finset.card + (n + 1) =
        --(Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground.erase v) (F.ground.erase v).powerset).sum Finset.card + 1
        --#check Finset.sum_bij i hi i_inj i_surj comm
        --Finset.sum_bij i hi i_inj i_surj comm : ∑ x ∈ domain, ff x = ∑ x ∈ range, gg x
        let sumcard := Finset.sum_bij i hi i_inj i_surj comm
        dsimp [domain,range,ff,gg] at sumcard
        --∑ x ∈ Finset.filter (fun s => F.sets s) F.ground.powerset, x.card =
        -- ∑ x ∈ Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground.erase v) (F.ground.erase v).powerset,
        -- if x = F.ground.erase v then x.card + 1 else x.card := Finset.sum_bij i hi i_inj i_surj comm

        convert sumcard

        have lem_eq: (Finset.filter (fun s => (F.sets s ∧ v ∉ s) ∨ s = F.ground.erase v) (F.ground.erase v).powerset).sum Finset.card
         =  (Finset.filter (fun s => F.sets s ∨ s = F.ground.erase v) (F.ground.erase v).powerset).sum Finset.card := by
          apply Finset.sum_congr
          simp_all only [ge_iff_le, idealDelF]
          ext1 a
          rw [Finset.mem_filter]
          rw [Finset.mem_powerset]
          rw [Finset.mem_filter]
          rw [Finset.mem_powerset]
          constructor
          · intro a_1
            constructor
            exact a_1.1
            --#check a_1.right
            cases a_1.right with
            | inl lt =>
              exact Or.inl lt.left
            | inr ri =>
              cases a_1.right with
              | inl left =>
                exact Or.inl left.1
              | inr right =>
                exact Or.inr right
          · intro a_1
            constructor
            exact a_1.1
            have vna: v ∉ a := by
              let a11 := a_1.1
              rw [←hv_equal] at a11
              rw [Finset.subset_erase] at a11
              exact a11.2
            cases a_1.2 with
            | inl lt =>
              exact Or.inl ⟨lt, vna⟩
            | inr ri =>
              exact Or.inr ri
          · intro a_1
            intro _
            rfl
          /-
          apply Iff.intro
          · intro a_2
            cases a_2 with
            | inl h => simp_all only [true_or]
            | inr h_1 =>
              subst h_1
              simp_all only [subset_refl, or_true]
          · intro a_2
            cases a_2 with
            | inl h =>
              left
              constructor
              exact h
              rw [←hv_equal] at a_1
              rw [Finset.subset_erase] at a_1
              simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, not_false_eq_true, domain]
            | inr h_1 =>
              subst h_1
              simp_all only [subset_refl, Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true,
                or_true]
          · intro a_2
            intro _
            simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, idealDelF]
            -/
        --成り立つが使ってない。
        /-
        have lem_eq1: (Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground.erase v) (F.ground.erase v).powerset).sum Finset.card
         = (Finset.filter (fun s => F.sets s ∨ s = F.ground.erase v) (F.ground.erase v).powerset).sum Finset.card := by
          apply Finset.sum_congr
          simp_all only [ge_iff_le, idealDelF]
          ext1 a
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_congr_right_iff]
          intro a_1
          apply Iff.intro
          · intro a_2
            cases a_2 with
            | inl h => simp_all only [true_or]
            | inr h_1 =>
              subst h_1
              simp_all only [subset_refl, or_true]
          ·intro a_2
           cases a_2 with
           | inl h =>
             simp_all only [true_and]
             constructor
             -- a_1  : a ⊆ F.ground.erase vからgoal v notin aは言えるのでは。
             let vng :=  (Finset.not_mem_erase v F.ground)
             by_contra h_contra
             let vng2 := a_1 h_contra
             apply vng
             simp_all only [vng2]
           | inr h_1 =>
             subst h_1
             simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true, or_true]
          ·intro a_2
           intro a
           simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, idealDelF]

        have lem_eq2: (Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground.erase v) (F.ground.erase v).powerset).sum Finset.card + 1
         = (Finset.filter (fun s => F.sets s ∨ s = F.ground.erase v) (F.ground.erase v).powerset).sum Finset.card + 1 := by
           rw [lem_eq1]
        -/

        have lem_prop:∀ (s:Finset (Fin (n+1))), s ∈ (F.ground.erase v).powerset → ¬ ((F.sets s ∧ v ∉ s) ∧ s = F.ground.erase v) := by
          intro s _
          intro h
          --hv_hyperedge : ¬F.sets (F.ground \ {v})単にこれを使うだけの証明かも。
          obtain ⟨left, right⟩ := h
          rw [right] at left
          let left1 := left.1

          rw [hv_equal] at left1
          contradiction

        --#check total_degone_card F.toSetFamily v hv_left degree_one F.univ_mem hcard0
        let leftset := Finset.filter (fun s => F.sets s ∧ v ∉ s) (F.ground.erase v).powerset
        let rightset := Finset.filter (fun s => s = F.ground.erase v) (F.ground.erase v).powerset
        --let hcap:= degree_one_hyperedges_partition2 F v hv_left --hv_singleton
        --以下を示す方針は正しそう。
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
            simp_all only [ge_iff_le, Finset.mem_erase, ne_eq, not_true_eq_false, and_true]
          have sgs: F.sets s := by
            subst sg
            simp_all only [ge_iff_le, Finset.mem_powerset, not_and, and_imp, subset_refl, Finset.mem_erase, ne_eq,
              not_true_eq_false, and_true, not_false_eq_true, true_and, and_self, idealDelF]
          rw [sg] at sgs
          rw [hv_equal] at sgs
          exact hv_hyperedge sgs

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
        --lemma filter_sum {α : Type} [DecidableEq α] [Fintype α] {P Q : Finset α → Prop} [DecidablePred P] [DecidablePred Q] (S : Finset (Finset α))  :
        --(∀ (s:Finset α), ¬(P s ∧ Q s)) →
        --(Finset.filter (λ (s : Finset α) => P s ∨ Q s) S).sum Finset.card
        -- = ((Finset.filter (λ (s : Finset α) => P s) S).sum Finset.card) +
        -- (Finset.filter (λ (s : Finset α) => Q s) S).sum Finset.card
          exact filter_sum_func (F.ground.erase v).powerset gg lem_prop
        rw [←hv_equal]
        rw [sum_lem]

        rw [filter_sum  (λ s => (F.sets s ∧ v ∉ s)) (λ s => s = F.ground.erase v) (F.ground.erase v).powerset disjoint2]

        dsimp [gg]
        simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, Finset.mem_erase, ne_eq, not_true_eq_false,
          false_and, not_false_eq_true, and_true, and_imp, subset_refl, exists_prop, Finset.singleton_subset_iff,
          Finset.sdiff_subset]

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
              simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, Finset.sdiff_subset, and_self,
                not_true_eq_false, domain]
            subst hx_eq
            simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, Finset.sdiff_subset, and_self,
              not_true_eq_false]
          · case neg =>
            --x.card = if x = F.ground \ {v} then (F.ground \ {v}).card + 1 else x.card
            simp [hx_eq]

        have sum_part2: ∑ x ∈ (Finset.filter (fun s => s = F.ground.erase v) (F.ground.erase v).powerset), x.card = F.ground.card - 1 := by
          have h_filter : Finset.filter (λ s => s = F.ground.erase v) (F.ground.erase v).powerset = {F.ground.erase v} :=
            by
              ext s
              simp [Finset.mem_powerset, Finset.mem_filter, Finset.subset_iff]
              intro hh
              intro x hx
              constructor
              · rw [hh] at hx
                rw [Finset.mem_erase] at hx
                exact hx.1
              · rw [hh] at hx
                rw [Finset.mem_erase] at hx
                exact hx.2
          rw [h_filter]
          rw [Finset.sum_singleton]
          exact Finset.card_erase_of_mem hv_left

        have sum_part3: ∑ x ∈ (Finset.filter (fun s => s = F.ground) (F.ground.powerset)), x.card = F.ground.card := by
          have h_filter : Finset.filter (λ s => s = F.ground) (F.ground.powerset) = {F.ground} :=
            by
              ext s
              simp [Finset.mem_powerset, Finset.mem_filter, Finset.subset_iff]
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
                simp [Finset.mem_powerset, Finset.mem_filter, Finset.subset_iff]
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

            --rw [if_pos]
            rw [Finset.card_erase_of_mem hv_left]
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
        --total_eqの証明が終わった。あとは、number_eqとtotal_eqを使って、goalを証明する。
      rw [number_eq]
      rw [total_eq]

      --let tsoh := total_size_of_hyperedges idealDelF.toSetFamily
      let noh := number_of_hyperedges idealDelF.toSetFamily
      have induction_assum: (total_size_of_hyperedges idealDelF.toSetFamily + 1) * 2 ≤
             (number_of_hyperedges idealDelF.toSetFamily) * F.ground.card := by
        have h_assum_case: idealDelF.ground.card = n := by
          omega
        have h_assum_card0: idealDelF.ground.card = F.ground.card -1 := by
          --have hcard1: idealDelF.ground.card = n := by
          --  omega
          rw [h_assum_case]
          rw [hcard]
          omega
        have h_assum_card1: idealDelF.ground.card ≥ 1 := by
          omega
        --#check IdealFamily.deletionToN nposi idealDelF v hvfideal h_assum_card1
        let idealDelFn := @IdealFamily.deletionToN (Fin (n + 1)) n nposi idealDelF v hvfideal h_assum_card1
        --#check h_ind (IdealFamily.deletionToN nposi idealDelF v hvfideal h_assum_card1)
        have hcard2: idealDelFn.ground.card = n := by
          have subs: idealDelFn = @IdealFamily.deletionToN (Fin (n + 1)) n nposi idealDelF v hvfideal h_assum_card1 := by
            rfl
          rw [subs]

          have eqset: idealDelFn.ground = Finset.image (finDrop nposi v) idealDelF.ground := by
            rw [subs]
            dsimp [IdealFamily.deletionToN]
          have eqcard: idealDelFn.ground.card = idealDelF.ground.card := by
            rw [eqset]
            --rw [Finset.card_image_of_injective]
            --lemma finDropCardEq {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (s : Finset (Fin (n+1))) (hvx: v ∉ s)
            exact finDropCardEq nposi v idealDelF.ground hvfideal
          rw [eqcard]
          simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, and_self, Finset.mem_erase, ne_eq,
            not_true_eq_false, false_and, not_false_eq_true, and_true, and_imp, subset_refl, Finset.sdiff_subset,
            Finset.singleton_subset_iff, exists_prop, add_tsub_cancel_right, idealDelF, domain, i, range, idealDelFn]

        let result := (h_ind.2 idealDelFn) hcard2
        --#check result
        dsimp [normalized_degree_sum] at result
        rw [hcard2] at result
        --dsimp [idealDelFn] at result
        --deletonToNをしても、total_sizeもnumber_of_hyperedgesも変わらないという定理を最後に適用する必要がある。
        --lemma IdealFamily.deletionToN_number {n : ℕ} (nposi : n ≥ 1) (F : IdealFamily (Fin (n + 1))) (v : Fin (n + 1)) (hvf : v ∉ F.ground)
        --(gcard : F.ground.card ≥ 1) : number_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi F v hvf gcard).toSetFamily = number_of_hyperedges F.toSetFamily
        have eqcard_number: number_of_hyperedges idealDelF.toSetFamily = number_of_hyperedges idealDelFn.toSetFamily := by
          have hcard2_ge1: idealDelF.ground.card ≥ 1 := by
            simp_all only [ge_iff_le]
          exact Eq.symm (IdealFamily.deletionToN_number nposi idealDelF v hvfideal hcard2_ge1)
        simp only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, and_self, Finset.mem_erase, ne_eq,
          not_true_eq_false, false_and, not_false_eq_true, and_true, and_imp, subset_refl, Finset.sdiff_subset,
          Finset.singleton_subset_iff, exists_prop, add_tsub_cancel_right, tsub_le_iff_right, zero_add, idealDelF,
          idealDelFn, domain, i, range]
        --lemma deletion_total: ∀ (n : ℕ) (F : IdealFamily (Fin (n + 1))) (nposi : n ≥ 1) (v : Fin (n + 1)) (hvf : v ∉ F.ground) (gcard : F.ground.card ≥ 1),
        --total_size_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi F v hvf gcard).toSetFamily = total_size_of_hyperedges F.toSetFamily
        have eqcard_total: total_size_of_hyperedges idealDelF.toSetFamily = total_size_of_hyperedges idealDelFn.toSetFamily := by
          exact Eq.symm (deletion_total n idealDelF nposi v hvfideal h_assum_card1)
        rw [←eqcard_number] at result
        rw [←eqcard_total] at result
        dsimp [idealDelF] at result
        --dsimp [IdealFamily.deletionToN]
        --#check (IdealFamily.deletionToN nposi (IdealDeletion.idealdeletion F v hv_left hcard0) v hvfideal h_assum_card1)
        let idealDelFn2 := (@IdealFamily.deletionToN (Fin (n + 1)) n nposi (IdealDeletion.idealdeletion F v hv_left hcard0) v hvfideal h_assum_card1)
        have eqlem0: idealDelFn = idealDelFn2 := by
          rfl

        have eqlem: number_of_hyperedges (idealDelFn.toSetFamily) = number_of_hyperedges (IdealDeletion.idealdeletion F v hv_left hcard0).toSetFamily := by
          simp_all only [subset_refl, Finset.singleton_subset_iff, Finset.sdiff_subset, idealDelFn, idealDelF,
            idealDelFn2]
        --基本的な変数を文字でおいて整理する。--ゴールとresultを[idealDelFn]を使って書き換える。
        have subs1: idealDelF = IdealDeletion.idealdeletion F v hv_left hcard0:= by
          rfl
        have subs2: number_of_hyperedges idealDelF.toSetFamily = number_of_hyperedges (IdealDeletion.idealdeletion F v hv_left hcard0).toSetFamily := by
           rfl
        have subs3: total_size_of_hyperedges idealDelF.toSetFamily = total_size_of_hyperedges (IdealDeletion.idealdeletion F v hv_left hcard0).toSetFamily := by
           rfl

        rw [←subs1] at result
        simp
        ring_nf
        rw [←subs2]
        rw [←subs3]
        rw [hcard]

        --result : ↑(total_size_of_hyperedges idealDelF.toSetFamily) * 2 ≤ ↑(number_of_hyperedges idealDelF.toSetFamily) * ↑n
        --goal : 2 + total_size_of_hyperedges idealDelF.toSetFamily * 2 ≤ number_of_hyperedges idealDelF.toSetFamily + number_of_hyperedges idealDelF.toSetFamily * n


        --rw [←tsoh] at result
        --rw [←noh] at result
        /-have idealDelF_univ_mem: idealDelF.sets (F.ground \ {v}) :=
          by
            have eqground: idealDelF.ground = F.ground \ {v}:= by
              dsimp [idealDelF]
              rw [IdealDeletion.idealdeletion]
              simp
              rw [hv_equal]
            rw [←eqground]
            exact idealDelF.univ_mem

        have idealDelF_empty_mem: idealDelF.sets ∅ := by
          exact idealDelF.empty_mem
        --こんなことを証明しなくても、台集合の1以上のidealは、常にhyperedgeが2つ以上ある。
        -/
        -- 台集合 ground の大きさが 1 以上の IdealFamily で number_of_hyperedges が 2 以上であることの証明

        have eqlem2: 2 ≤ noh := by
          dsimp [noh]
          dsimp [number_of_hyperedges]
          --dsimp [idealDelF]
          --F.gound - vとF.empty_memより、hyperedgeは2つ以上。
          exact hyperedges_card_ge_two idealDelF h_assum_card1

        linarith
      rw [hcard] at induction_assum ⊢
      ring_nf
      ring_nf at induction_assum
      --induction_assum : 2 + total_size_of_hyperedges idealDelF.toSetFamily * 2 ≤
      --number_of_hyperedges idealDelF.toSetFamily + number_of_hyperedges idealDelF.toSetFamily * n
      simp_all
      --rw [←tsoh]
      --rw [←noh]
      --rw [←tsoh] at induction_assum
      --rw [←noh] at induction_assum
      --induction_assum : 2 + tosh * 2 ≤ noh * (n + 1)
      --goal : 2 + tosh * 2 ≤ noh * n + noh
      linarith

end Ideal