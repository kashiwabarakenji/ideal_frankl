import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne
import rooted.functionalCommon
--import rooted.functionalTreePreorder
import rooted.functionalTreePartialorder
import rooted.functionalSPO
import rooted.functionalSPO2
import rooted.functionalTreeIdeal

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]


noncomputable def setoid_ideal_injection_domain (s : Setup_spo α)(q : Quotient s.setoid ): Finset (Finset s.V) :=
   s.V.attach.powerset.filter (fun (ss:Finset s.V) => (spo_closuresystem s).sets (ss.image Subtype.val)  ∧ (classOf s q) ⊆ ss)

noncomputable def setoid_ideal_injection_codomain (s : Setup_spo α)(q : Quotient s.setoid ) : Finset (Finset s.V) :=
   s.V.attach.powerset.filter (fun (ss:Finset s.V) => (spo_closuresystem s).sets (ss.image Subtype.val)  ∧ ¬(classOf s q) ⊆ ss)

noncomputable def setoid_ideal_injection (s: Setup_spo α)(q : Quotient s.setoid ) (hm: isMaximal_spo s q) : setoid_ideal_injection_domain s q → setoid_ideal_injection_codomain s q :=
  fun ⟨ss, hss⟩ => ⟨ss \ (classOf s q), by
  dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain]
  rw [Finset.filter, Finset.powerset]
  simp
  constructor
  · use (ss \ classOf s q).val
    have hss_dom : ss ∈ setoid_ideal_injection_domain s q := by
      exact hss
    have h_subset : ss ⊆ s.V.attach := by
      apply Finset.mem_powerset.mp
      simp_all only [Finset.mem_powerset]
      intro x hx
      simp_all only [mem_attach]
    have diff_subset : ss \ classOf s q ⊆ s.V.attach := by
      intro x hx
      simp_all only [mem_sdiff, mem_attach]
    constructor
    · apply congrFun rfl
    · exact val_le_iff_val_subset.mpr diff_subset
  · constructor
    · --qを除いてもidealであることを示す必要。ここの部分は、極大性を利用する必要がある。
      dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain]
      dsimp [spo_closuresystem]
      --qの生成するidealをuseすればよいか。でも連結とは限らない。
      --ssに対応するQuotientをuseすればよいか。
      --Setup_spoにおいて、ssに対して、そのQuotientの集合を与える関数を作ってもいいかも。
      use QuotientOf s (ss \ (classOf s q))
      constructor
      · intro qq hqq q' hq'
        dsimp [QuotientOf]
        dsimp [QuotientOf] at hqq
        rw [Finset.mem_image] at hqq
        rw [Finset.mem_image]
        use Quotient.out q'
        constructor
        · --hq'から言えるはず。hq' : q' ≤ qq
          show q'.out ∈ ss \ classOf s q
          sorry
        · simp_all only [Subtype.exists, Quotient.out_eq]
      · simp
        constructor
        ·
          rename_i x
          obtain ⟨val, property⟩ := x
          intro x hx
          simp_all only [Finset.mem_image, mem_sdiff, Subtype.exists, exists_and_right, exists_eq_right]
          obtain ⟨w, h⟩ := hx
          obtain ⟨left, right⟩ := h
          simp_all only
        · intro hs
          constructor
          · intro x hx h
            dsimp [QuotientOf]
            rw [Finset.mem_image]
            use ⟨x, hx⟩
            constructor
            · simp_all only [mem_sdiff, not_false_eq_true, and_self]
            · simp_all only

          · intro q_1 hq_1 a ha hha
            dsimp [QuotientOf] at hq_1
            rw [Finset.mem_image] at hq_1
            obtain ⟨w, hq_1⟩ := hq_1
            constructor
            · --hhaとhq_1を使う。必要であれば補題を作る。ssはsetoidで閉じている。
              show ⟨a, ha⟩ ∈ ss
              have wss: w ∈ ss := by
                rw [@mem_sdiff] at hq_1
                exact hq_1.1.1
              have srwa: (s.setoid).r w ⟨a, ha⟩:= by
                subst hha
                simp_all only [mem_sdiff, true_and, Quotient.eq]
              dsimp [setoid_ideal_injection_domain,] at hss
              rw [Finset.mem_filter] at hss
              dsimp [spo_closuresystem] at hss
              obtain ⟨hss, hss'⟩ := hss --分解できないのはimpliesの形式かも。
              --hss'は、domainに入っているideal全体か。
              obtain ⟨hss', hss''⟩ := hss'
              obtain ⟨hss', hss'''⟩ := hss'
              obtain ⟨hss', hss''''⟩ := hss'
              simp at hss'''
              obtain ⟨hss''', hss5⟩ := hss'''
              obtain ⟨hss5, hss6⟩ := hss5
              have :Finset.image Subtype.val ss ⊆ s.V := by
                subst hha
                simp_all only [Finset.mem_powerset, forall_true_left, mem_sdiff, true_and, Quotient.eq, and_true]
              specialize hss6 this
              obtain ⟨h_to, h_from⟩ := hss6
              specialize h_from q_1
              dsimp [isMaximal_spo] at hm
              specialize hm q_1
              have : q_1 ∈ hss' := by
                --hss''' ∀ q ∈ hss', ∀ q' ≤ q, q' ∈ hss'
                apply hss''' q
                · --goal : q ∈ hss'
                  -- q ≤ q_1 → q_1 ≤ q
                  sorry
                · sorry
              rename_i x this_1
              subst hha
              simp_all only [Subtype.coe_eta, Finset.mem_powerset, mem_sdiff, Quotient.eq, true_and, and_true,
                forall_const]
              obtain ⟨val, property⟩ := x
              obtain ⟨val_1, property_1⟩ := w
              apply h_from
              rfl

            · show ⟨a, ha⟩ ∉ classOf s q
              dsimp [classOf]
              rw [Finset.mem_filter]
              simp
              show ¬Quotient.mk'' ⟨a, ha⟩ = q
              --hq_1 : w ∈ ss \ classOf s q ∧ ⟦w⟧ = q_1
              sorry





    · have :(classOf s q).Nonempty := by --使っているみたい。
        exact classOf_nonempty s q
      rw [@subset_sdiff]
      simp_all only [disjoint_self, Finset.bot_eq_empty, not_and]
      intro a
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      simp_all only [Finset.not_nonempty_empty, disjoint_self, Finset.bot_eq_empty, not_and]
⟩
theorem setoid_ideal_rare (s : Setup_spo2 α)(q : Quotient (s.toSetup_spo).setoid )(hm: isMaximal_spo s.toSetup_spo q) :
  ∀ (x : classOf s.toSetup_spo q), (spo_closuresystem s.toSetup_spo).toSetFamily.is_rare x := by
sorry
