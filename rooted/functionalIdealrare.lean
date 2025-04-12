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
  have hss_dom : ss ∈ setoid_ideal_injection_domain s q := by
    exact hss
  have h_subset : ss ⊆ s.V.attach := by
    apply Finset.mem_powerset.mp
    simp_all only [Finset.mem_powerset]
    intro x hx
    simp_all only [mem_attach]

  dsimp [setoid_ideal_injection_domain] at hss
  rw [Finset.mem_filter] at hss
  dsimp [spo_closuresystem] at hss
  obtain ⟨hss, hss'⟩ := hss --分解できないのはimpliesの形式かも。
  --hss'は、domainに入っているideal全体か。
  obtain ⟨hss', hss''⟩ := hss'
  --この段階で、hss'は、idealの要素になる条件がはいっている。
  obtain ⟨sqq', hss'''⟩ := hss'
  --sqq'は、idealの要素となるquotientの集合。
  simp at hss'''
  obtain ⟨hss''', hss5⟩ := hss'''
  obtain ⟨hss5, hss6⟩ := hss5
  have :Finset.image Subtype.val ss ⊆ s.V := by
    simp_all only [Finset.mem_powerset, forall_true_left, mem_sdiff, true_and, Quotient.eq, and_true]
  specialize hss6 this
  obtain ⟨h_to, h_from⟩ := hss6

  constructor
  · use (ss \ classOf s q).val

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
          rw [Finset.mem_sdiff]
          obtain ⟨w, hqq⟩ := hqq
          obtain ⟨left, right⟩ := hqq
          rw [@mem_sdiff] at left
          have :s.setoid.r w qq.out := by
            apply s.setoid.trans (s.setoid.refl w)
            exact Quotient.mk_eq_iff_out.mp right
            --f_fromが関係ありそう。

          have qqs:qq ∈ sqq' := by
            simp_all only [Finset.mem_powerset, coe_mem, Subtype.coe_eta, Quotient.eq, forall_const]
            subst right
            simp_all only [coe_mem, Subtype.coe_eta, Quotient.eq, forall_const]
          specialize h_from
          have : qq.out ∈ ss := by
            specialize h_from qq
            rename_i x this_1 this_2
            subst right
            simp_all only [Finset.mem_powerset, Subtype.coe_eta, true_and, coe_mem, Quotient.eq]
            obtain ⟨val_1, property_1⟩ := w
            apply h_from
            · simp_all only [forall_const]
            · simp_all only [forall_const, Subtype.coe_eta]
              obtain ⟨val, property⟩ := this_1
              symm
              exact this
          have qsq:q' ∈ sqq' := by
            exact hss''' qq qqs q' hq'


          constructor
          · show q'.out ∈ ss
            specialize h_from q'
            specialize  h_from qsq
            subst right
            simp_all only [Finset.mem_powerset, coe_mem, Subtype.coe_eta, Quotient.out_eq]
          · show q'.out ∉ classOf s q
            --goal q'.out ∉ classOf s q
            --left : w ∈ ss ∧ w ∉ classOf s q
            -- hq' : q' ≤ qq
            -- right : ⟦w⟧ = qq
            -- hm : isMaximal_spo s q
            dsimp [isMaximal_spo] at hm
            have qneq:q' ≠ q := by
              intro h_contra
              have :qq = q := by
                rw [h_contra] at hq'
                have qq_q: s.spo.le qq q := by
                  apply (hm qq)
                  subst right h_contra
                  simp_all only [Finset.mem_powerset, coe_mem, Subtype.coe_eta]
                have q_qq:s.spo.le q qq := by
                  subst right h_contra
                  simp_all only [Finset.mem_powerset, coe_mem, Subtype.coe_eta]
                apply s.spo.le_antisymm
                · subst right h_contra
                  simp_all only [Finset.mem_powerset, coe_mem, Subtype.coe_eta]
                · exact hq'
              --rw [←this] at h_contra
              --rightとleftに矛盾することをいう。
              rw [←right] at this
              rw [←this] at left
              let left2 := left.2
              simp  at left2
              dsimp [classOf] at left2
              rw [Finset.mem_filter] at left2
              simp at left2
            intro h_contra
            dsimp [classOf] at h_contra
            rw [Finset.mem_filter] at h_contra
            have : q=q' := by
              subst right
              simp_all only [Finset.mem_powerset, ne_eq, mem_attach, Quotient.out_eq, and_false]
            rw [this] at qneq
            contradiction
        · simp_all only [Subtype.exists, Quotient.out_eq]
      · --(ss \ classOf s q).valがidealの要素であることを示す。
        simp
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
          --idealの要素になるためには、下のものがssにはいることと、
          constructor
          · intro x hx h
            dsimp [QuotientOf]
            rw [Finset.mem_image]
            use ⟨x, hx⟩
            constructor
            · simp_all only [mem_sdiff, not_false_eq_true, and_self]
            · simp_all only

          · --ssの元の同値類を考えて、その要素を持ってきたら、またssの要素。大小は関係ないかも。qが極大であることも使わないかも。
            intro q_1 hq_1 a ha hha
            specialize h_from q_1  --これは正しいのか。
            dsimp [QuotientOf] at hq_1
            rw [Finset.mem_image] at hq_1
            obtain ⟨w, hq_1⟩ := hq_1
            rw [@mem_sdiff] at hq_1
            dsimp [isMaximal_spo] at hm
            specialize hm q_1
            have srwa: (s.setoid).r w ⟨a, ha⟩:= by
              subst hha
              simp_all only [mem_sdiff, true_and, Quotient.eq]
            have : q_1 ∈ sqq' := by
              specialize h_to w
              subst hha
              simp_all only [Finset.mem_powerset, coe_mem, Subtype.coe_eta, forall_const, Quotient.eq, true_and,
                and_true]

            constructor
            · --hhaとhq_1を使う。hha : ⟦⟨a, ha⟩⟧ = q_1。hq_1 : w ∈ ss \ classOf s q ∧ ⟦w⟧ = q_1。必要であれば補題を作る。ssはsetoidで閉じている。
              --h_fromも使うかも。
              show ⟨a, ha⟩ ∈ ss
              have wss: w ∈ ss := by
                exact hq_1.1.1

              rename_i x this_1
              subst hha
              simp_all only [Subtype.coe_eta, Finset.mem_powerset, mem_sdiff, Quotient.eq, true_and, and_true,
                forall_const]
              apply h_from
              rfl

            · show ⟨a, ha⟩ ∉ classOf s q
              dsimp [classOf]
              rw [Finset.mem_filter]
              simp
              show ¬Quotient.mk'' ⟨a, ha⟩ = q
              --hq_1 : w ∈ ss \ classOf s q ∧ ⟦w⟧ = q_1は使いそう。
              --srwa: (s.setoid).r w ⟨a, ha⟩:= by
              have : q_1 ≠ q := by
                intro h_contra
                obtain ⟨hq_11, hq_12⟩ := hq_1
                rw [←h_contra] at hq_11
                rw [←hq_12] at hq_11
                dsimp [classOf] at hq_11
                rw [Finset.mem_filter] at hq_11
                simp at hq_11
              subst hha
              simp_all only [Finset.mem_powerset, Quotient.eq, forall_const, Subtype.coe_eta, true_and, and_true,
                ne_eq, not_false_eq_true]

    · have :(classOf s q).Nonempty := by --使っているみたい。
        exact classOf_nonempty s q
      rw [@subset_sdiff]
      simp_all only [disjoint_self, Finset.bot_eq_empty, not_and]
      intro a
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      simp_all only [Finset.not_nonempty_empty, disjoint_self, Finset.bot_eq_empty, not_and]
⟩

theorem setoid_ideal_injection_injective
  (s : Setup_spo α) (q : Quotient s.setoid) (hm : isMaximal_spo s q) :
  Function.Injective (setoid_ideal_injection s q hm) := by
  intro ⟨ss₁, h₁⟩ ⟨ss₂, h₂⟩ h_eq
  simp only [setoid_ideal_injection] at h_eq

  -- 差集合が等しい → 元の集合が等しいことを示す
  -- ss₁ = (ss₁ \ classOf s q) ∪ classOf s q
  have h₁_subset : classOf s q ⊆ ss₁ := by
    dsimp [classOf]
    dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain] at h₁
    dsimp [spo_closuresystem] at h₁
    simp_all only [Subtype.mk.injEq]
    simp_all
    obtain ⟨left, right⟩ := h₁
    obtain ⟨left_1, right⟩ := right
    obtain ⟨w, h⟩ := left_1
    obtain ⟨left_1, right_1⟩ := h
    obtain ⟨left_2, right_1⟩ := right_1
    simp_all only [forall_true_left]
    obtain ⟨left_3, right_1⟩ := right_1
    exact right

  have h₁_union : ss₁ = (ss₁ \ classOf s q) ∪ (classOf s q) :=
  by
    symm
    apply Finset.sdiff_union_of_subset
    dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain] at h₁
    simp_all only [Subtype.mk.injEq]

  -- powerset の要素なので classOf s q ⊆ ss₁, ss₂
  have h₂_subset : classOf s q ⊆ ss₂ := by
    dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain] at h₂
    dsimp [spo_closuresystem] at h₂
    dsimp [classOf]
    sorry

  -- Finset.sdiff_union_of_subset : A = (A \ B) ∪ B  (if B ⊆ A)
  have eq₂ : ss₂ = (ss₂ \ classOf s q) ∪ classOf s q :=
  by
    exact Eq.symm (sdiff_union_of_subset h₂_subset)

  -- ここで eq_sdiff を使い、差集合が等しいので右辺も等しくなる
  have : ss₁ = ss₂ := by
    rw [h₁_union]
    rw [eq₂]
    have :ss₁ \ classOf s q  = ss₂ \ classOf s q := by
      rw [@Subtype.mk_eq_mk] at h_eq
      exact h_eq
    rw [this]

  exact Subtype.mk_eq_mk.mpr this


theorem setoid_ideal_rare (s : Setup_spo2 α)(q : Quotient (s.toSetup_spo).setoid )(hm: isMaximal_spo s.toSetup_spo q) :
  ∀ (x : classOf s.toSetup_spo q), (spo_closuresystem s.toSetup_spo).toSetFamily.is_rare x := by
sorry
