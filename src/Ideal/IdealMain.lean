--Ideal集合族が平均abundantにならないことの証明が目標。まだうまく行ってないが保留にする。
import Mathlib.Data.Finset.Basic --hiding eq_empty_of_subset_empty
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import Ideal.IdealDeletion
import Ideal.IdealRare
import Ideal.IdealSum
import Ideal.IdealNumbers
import Ideal.IdealSimple
import Ideal.IdealDegreeOne
import Ideal.IdealFin
import Ideal.IdealDegOneMain
import LeanCopilot
set_option maxHeartbeats 1000000

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]



--def P (x:Nat) : Prop := x ≥ 2  ∧ ∀ (F: IdealFamily (Fin x)), F.ground.card = x → normalized_degree_sum F.toSetFamily ≤ 0

theorem induction_step {n:Nat} (hn: n >= 2) (h_ind: P n) : P (n+1) := by
  -- ここでFintypeインスタンスを明示的に使用
  --have fintype_ground : Fintype F.ground := finF
  have nposi : n ≥ 1 := by omega
  unfold P at h_ind ⊢
  obtain ⟨h_ge2, h_ind⟩ := h_ind

  constructor
  simp_all only [ge_iff_le, Nat.reduceLeDiff]
  --obtain ⟨left, right⟩ := h
  --omega
  intros F hcard
   -- n ≥ 2 から n + 1 ≥ 3 を導く
  have hcard0: F.ground.card >= 2 := by
    have h1 : n + 1 ≥ 3 := Nat.succ_le_succ hn
    -- F.ground.card = n + 1 なので、F.ground.card ≥ 3
    rw [←hcard] at h1
    -- F.ground.card ≥ 3 なので F.ground.card ≥ 2 も成立
    exact Nat.le_of_succ_le h1

  obtain ⟨v, hv⟩ := ideal_version_of_frankl_conjecture F
    --#check hv
  obtain ⟨hv_left, hv_right⟩ := hv

  by_cases hv_singleton: F.sets {v}
  · case pos =>

    set Fdel := IdealDeletion.idealdeletion F v hv_left hcard0
    have Fvx: v ∉ Fdel.ground := by
      intro h
      simp_all only [ge_iff_le]
      dsimp [Fdel] at h
      --simp_all only [Fdel]
      dsimp [IdealDeletion.idealdeletion] at h
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true]

    have hcard1: Fdel.ground.card = n := by
      simp_all only [ge_iff_le]
      simp_all only [Fdel]
      rw [IdealDeletion.idealdeletion]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]

    have hcard2: Fdel.ground.card ≥ 1 := by
      simp_all only [ge_iff_le]

    --#check IdealFamily.deletionToN nposi Fdel v Fvx hcard2
    set h_idealdeletion := IdealFamily.deletionToN nposi Fdel v Fvx hcard2
    --IdealFamily (Fin (n + 1))になっているがFin nになってほしい。

    have hcard3: h_idealdeletion.ground.card = n := by
      dsimp [h_idealdeletion]
      dsimp [IdealFamily.deletionToN]
      rw  [finDropCardEq nposi v Fdel.ground Fvx]
      exact hcard1

    have h_del_card: (@IdealFamily.deletionToN (Fin n) n nposi (IdealDeletion.idealdeletion F v hv_left hcard0) v Fvx
                hcard2).ground.card = n := by
      simp_all only [ge_iff_le]
      simp_all only [ge_iff_le, implies_true, imp_self, forall_true_left, Fdel, h_idealdeletion]
      exact hcard3

    set Fcont :=  (IdealDeletion.contraction_ideal_family F v hv_singleton hcard0)
    have h_cont: Fcont.ground.card = n := by
      simp_all only [ge_iff_le]
      --simp_all only [IdealDeletion.contraction]
      simp_all only [ge_iff_le, implies_true, sub_left_inj, add_left_inj, add_right_inj, Fdel, Fcont]
      rw [IdealDeletion.contraction_ideal_family]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]
      rw [IdealDeletion.contraction]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]

    have h_cont2: Fcont.ground.card ≥ 1 := by
      simp_all only [ge_iff_le]

    have Fvx2: v ∉ Fcont.ground := by
      intro h
      simp_all only [ge_iff_le]
      dsimp [Fcont] at h
      simp_all only [Fcont]
      dsimp [IdealDeletion.contraction_ideal_family] at h
      dsimp [IdealDeletion.contraction] at h
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true]

    have h_cont_card: Fcont.ground.card = n := by
      simp_all only [ge_iff_le]

    have h_cont_card2: (IdealDeletion.contraction_ideal_family F v hv_singleton hcard0).ground.card = n:= by
      simp_all only [ge_iff_le]

    set h_contraction := IdealFamily.deletionToN nposi Fcont v Fvx2 h_cont2
    have h_cont_card3: h_contraction.ground.card = n := by
      simp_all only [ge_iff_le]
      dsimp [h_contraction]
      dsimp [IdealFamily.deletionToN]
      rw [finDropCardEq nposi v Fcont.ground Fvx2]
      exact h_cont_card

    dsimp [Fdel] at hcard1
    --#check (h_ind h_idealdeletion) hcard3
    let h_idealdeletion2 := h_ind h_idealdeletion hcard3
    --#check h_ind h_contraction
    let h_contraction2 := (h_ind h_contraction) h_cont_card3

    have eq1: ideal_degree F v = degree F.toSetFamily v := by
      simp only [ideal_degree, degree]

    have eq2: ideal_family_size F = number_of_hyperedges F.toSetFamily := by
      simp only [ideal_family_size, total_size_of_hyperedges]

    simp only [ge_iff_le, tsub_le_iff_right, zero_add, Fdel, Fcont] at h_idealdeletion2 h_contraction2  ⊢
    simp only [normalized_degree_sum] at h_idealdeletion2 h_contraction2  ⊢

    rw [IdealFamily.deletionToN_number nposi Fdel v Fvx hcard2] at h_idealdeletion2
    rw [IdealFamily.deletionToN_number nposi Fcont v Fvx2 h_cont2] at h_contraction2
    dsimp [h_idealdeletion] at h_idealdeletion2
    dsimp [h_contraction] at h_contraction2
    rw [deletion_total] at h_idealdeletion2 h_contraction2
    dsimp [Fdel] at h_idealdeletion2
    dsimp [Fcont] at h_contraction2
    rw [h_del_card] at h_idealdeletion2

    --以下の部分も場合分けの前に移動したほうがよいかも。
    --let total_del := (total_size_of_hyperedges ((@IdealFamily.deletionToN (Fin n) n nposi Fdel v Fvx hcard2):IdealFamily (Fin n)).1)
    set total_del := total_size_of_hyperedges (IdealDeletion.idealdeletion F v hv_left hcard0).1
    --set number_del := (number_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi Fdel v Fvx hcard2).1) with number_del
    set number_del := (number_of_hyperedges (IdealDeletion.idealdeletion F v hv_left hcard0).1)
    --let total_cont := (total_size_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi Fcont v Fvx2 h_cont2).1)
    --set total_cont := total_size_of_hyperedges (IdealDeletion.contraction F.1 v hv_left hcard0) with h_total_cont
    set total_cont := total_size_of_hyperedges (IdealDeletion.contraction_ideal_family F v hv_singleton hcard0).toSetFamily
    --let number_cont := (number_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi Fcont v Fvx2 h_cont2).1)
    --set number_cont := (number_of_hyperedges (IdealDeletion.contraction F.1 v hv_left hcard0)) with h_number_cont
    set number_cont := (number_of_hyperedges (IdealDeletion.contraction_ideal_family F v hv_singleton hcard0).toSetFamily)
    set total := (total_size_of_hyperedges F.toSetFamily)
    set  number := (number_of_hyperedges F.toSetFamily)
    set degreev := (degree F.toSetFamily v)

    classical
    by_cases hv_hyperedge:(F.sets (F.ground \ {v}))
    ·   case pos =>
        have h_sum_have := (hyperedge_average_have F v hv_left hcard0) hv_hyperedge hv_singleton
        --have h_idealdeletion := (IdealDeletion.idealdeletion F v hv_left hcard0)
        --#check sum_have
        let number_have :=  hyperedge_count_deletion_contraction_have_z F v hv_left hcard0 hv_hyperedge hv_singleton

        simp only [ge_iff_le, tsub_le_iff_right, zero_add, Fdel, Fcont] at h_sum_have number_have
        simp only [normalized_degree_sum] at h_sum_have number_have

        --今になって考えてみれば、Fin nを使わずにground setの大きさで議論する方法の方が良かった。
        simp_all only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one, degreev, number,
          h_idealdeletion, Fdel, Fcont, h_contraction, total_del, number_del, total_cont, number_cont, total, number_have]
        linarith

    ·   case neg =>
        --hv_hyperedge:(F.sets (F.ground \ {v}))が成り立たないケース。hv_singleton : ¬F.sets {v}のケースかも。どちらも未解決。
        have h_sum_none := hyperedge_average_none F v hv_left hcard0 hv_hyperedge hv_singleton
        have number_none := hyperedge_count_deletion_contraction_none F v hv_left hcard0 hv_hyperedge hv_singleton

        simp only [ge_iff_le, tsub_le_iff_right, zero_add, Fdel, Fcont] at h_sum_none number_none
        simp only [normalized_degree_sum] at h_sum_none number_none
        simp_all only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one, degreev, number, h_idealdeletion,
        Fdel, Fcont, h_contraction, total_del, number_del, total_cont, number_cont, total]
        linarith

  --case negがもう一つある。hv_singleton:(F.sets {v})が成り立たないケース。
  --hv_singleton:(F.sets {v})が成り立たないケース。tabでインデントを調整して見えるようになった。
  · case neg =>

        have h_indPn : P n := by
          unfold P
          exact ⟨h_ge2, h_ind⟩
        exact degonemain n F v hv_left hv_singleton hcard0 hcard h_indPn

end Ideal
