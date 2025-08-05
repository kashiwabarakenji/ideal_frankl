import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
--import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne
import rooted.functionalCommon
import rooted.functionalTreePartialorder
import rooted.functionalSPO
import rooted.functionalSPO2
import rooted.functionalTreeIdeal

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

instance subtype_decidable_eq {p : α → Prop} [DecidablePred p] : DecidableEq (Subtype p) :=
  fun ⟨a, _⟩ ⟨b, _⟩ =>
    if h : a = b then isTrue (Subtype.ext h)
    else isFalse (fun H => absurd (congrArg Subtype.val H) h)


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
  obtain ⟨hss, hss'⟩ := hss
  obtain ⟨hss', hss''⟩ := hss'

  obtain ⟨sqq', hss'''⟩ := hss'

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
    · dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain]
      dsimp [spo_closuresystem]



      use QuotientOf s (ss \ (classOf s q))
      constructor
      · intro qq hqq q' hq'
        dsimp [QuotientOf]
        dsimp [QuotientOf] at hqq
        rw [Finset.mem_image] at hqq
        rw [Finset.mem_image]
        use Quotient.out q'
        constructor
        · show q'.out ∈ ss \ classOf s q
          rw [Finset.mem_sdiff]
          obtain ⟨w, hqq⟩ := hqq
          obtain ⟨left, right⟩ := hqq
          rw [@mem_sdiff] at left
          have :s.setoid.r w qq.out := by
            apply s.setoid.trans (s.setoid.refl w)
            exact Quotient.mk_eq_iff_out.mp right

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
            specialize h_from q_1
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
            · show ⟨a, ha⟩ ∈ ss
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

    · have :(classOf s q).Nonempty := by
        exact classOf_nonempty s q
      rw [@subset_sdiff]
      simp_all only [disjoint_self, Finset.bot_eq_empty, not_and]
      intro a
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      simp_all only [Finset.not_nonempty_empty, disjoint_self, Finset.bot_eq_empty, not_and]
⟩

private lemma setoid_ideal_injection_injective
  (s : Setup_spo α) (q : Quotient s.setoid) (hm : isMaximal_spo s q) :
  Function.Injective (setoid_ideal_injection s q hm) := by
  intro ⟨ss₁, h₁⟩ ⟨ss₂, h₂⟩ h_eq
  simp only [setoid_ideal_injection] at h_eq

  have h₂_subset : classOf s q ⊆ ss₂ := by
    dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain] at h₂
    dsimp [spo_closuresystem] at h₂
    dsimp [classOf]
    simp_all only [Subtype.mk.injEq]
    simp_all
    obtain ⟨left, right⟩ := h₂
    obtain ⟨left_1, right⟩ := right
    exact right


  have h₁_subset : classOf s q ⊆ ss₁ := by
    dsimp [classOf]
    dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain] at h₁
    dsimp [spo_closuresystem] at h₁
    simp_all only [Subtype.mk.injEq]
    simp_all
    obtain ⟨left, right⟩ := h₁
    obtain ⟨left_1, right⟩ := right
    exact right

  have h₁_union : ss₁ = (ss₁ \ classOf s q) ∪ (classOf s q) :=
  by
    symm
    apply Finset.sdiff_union_of_subset
    dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain] at h₁
    simp_all only [Subtype.mk.injEq]

  -- Finset.sdiff_union_of_subset : A = (A \ B) ∪ B  (if B ⊆ A)
  have eq₂ : ss₂ = (ss₂ \ classOf s q) ∪ classOf s q :=
  by
    exact Eq.symm (sdiff_union_of_subset h₂_subset)

  have : ss₁ = ss₂ := by
    rw [h₁_union]
    rw [eq₂]
    have :ss₁ \ classOf s q  = ss₂ \ classOf s q := by
      rw [@Subtype.mk_eq_mk] at h_eq
      exact h_eq
    rw [this]

  exact Subtype.mk_eq_mk.mpr this


omit [Fintype α] [DecidableEq α] in
private lemma powerset_image {α β : Type*}[DecidableEq β]
  (s : Finset α) (f : α → β) :
  s.powerset.image (fun a => a.image f) = (s.image f).powerset := by
  ext t

  constructor
  · intro a
    simp_all only [Finset.mem_image, Finset.mem_powerset]
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    subst right
    rw [Finset.image_subset_iff]
    intro x a
    simp_all only [Finset.mem_image]
    exact ⟨x, left a, rfl⟩
  · intro ht
    let a := s.filter (fun x => f x ∈ t)
    rw [Finset.mem_image]
    use a
    constructor
    · apply mem_powerset.mpr
      simp_all only [Finset.mem_powerset, filter_subset, a]
    · ext y

      constructor
      ·
        intro a_1
        simp_all only [Finset.mem_powerset, Finset.mem_image, mem_filter, a]
        obtain ⟨w, h⟩ := a_1
        obtain ⟨left, right⟩ := h
        obtain ⟨left, right_1⟩ := left
        simp_all only [a]

      · intro hy

        have : y ∈ s.image f := by
          simp_all only [Finset.mem_powerset, Finset.mem_image, a]
          simpa [a] using ht hy--mem_of_mem_powerset ht hy
        obtain ⟨x, hx_s, rfl⟩ := mem_image.mp this
        simp_all only [Finset.mem_powerset, Finset.mem_image, mem_filter, a]
        obtain ⟨w, h⟩ := this
        obtain ⟨left, right⟩ := h
        use x

------------



--Utilizing the injectivity of "cards that received image after filter are equal."
-- It is used with card_filter_image_eq, but it seems easier to prove it directly.
private lemma card_of_image_filter_of_inj_on
  {α β : Type} [DecidableEq α] [DecidableEq β]
  (s : Finset α) (f : α → β) (p : α → Prop) [DecidablePred p]
  (hf : Set.InjOn f (s.filter p)) :
  ((s.filter p).image f).card = (s.filter p).card :=
by
  exact card_image_iff.mpr hf

private lemma card_filter_image_eq
  {α β : Type} [DecidableEq α] [DecidableEq β]
  (S₀ : Finset α) (φ : α → β) (P : β → Prop)
  [DecidablePred P]
  (hφ : Set.InjOn φ (S₀.filter (fun x => P (φ x)))) :
  (S₀.filter (fun x => P (φ x))).card = ((S₀.image φ).filter P).card :=
by
  let cif := card_of_image_filter_of_inj_on S₀ φ
  simp_all only [coe_filter]
  rw [filter_image]
  simp_all only [coe_filter, cif]

--This guarantees the injectivity when a Subtype is copied with val.
private lemma image_val_inj_on
  {α : Type*} [DecidableEq α]
  {V : Finset α}
  (S : Finset (Finset {x // x ∈ V})) :
  Set.InjOn (fun ss => ss.image Subtype.val) S.toSet :=
by
  intros x hx y hy h
  apply Finset.ext
  intro a
  constructor
  · intro ha
    have : ↑a ∈ Finset.image Subtype.val x := Finset.mem_image_of_mem _ ha
    simp_all only [mem_coe, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
      coe_mem, exists_const]
  · intro ha
    have : a.val ∈ x.image Subtype.val := by simp_all only [mem_coe, Finset.mem_image, Subtype.exists,
      exists_and_right, exists_eq_right, Subtype.coe_eta, coe_mem, exists_const]
    obtain ⟨a', ha', hval⟩ := Finset.mem_image.mp this
    have : a = a' := by
      simp_all only [mem_coe, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
        coe_mem, exists_const]
      obtain ⟨val, property⟩ := a
      obtain ⟨val_1, property_1⟩ := a'
      subst hval
      simp_all only
    rw [this]; exact ha'

--If you copy the powerset consisting of the --attached elements with val, it returns to the original powerset.I'm using it below.
private lemma powerset_image_attach {α : Type*} [DecidableEq α] (V : Finset α) :
  Finset.image (fun ss => ss.image Subtype.val) V.attach.powerset = V.powerset := by
  apply Finset.ext
  intro s
  constructor
  · intro h
    obtain ⟨ss, hss, rfl⟩ := Finset.mem_image.mp h
    apply Finset.mem_powerset.mpr
    intro x hx
    simp_all only [Finset.mem_powerset, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    obtain ⟨w, h⟩ := h
    obtain ⟨w_1, h_1⟩ := hx
    obtain ⟨left, right⟩ := h
    simp_all only
  · intro h
    let ss := V.attach.filter (fun ⟨x, _⟩ => x ∈ s)
    have hss : ss ∈ V.attach.powerset := by
      simp_all only [Finset.mem_powerset, filter_subset, ss]
    have hS : ss.image Subtype.val = s := by
      ext a
      simp [ss]
      intro a_1
      simp_all only [Finset.mem_powerset, filter_subset, ss]
      exact h a_1
    rw [Finset.mem_image]
    exact ⟨ss, hss, hS⟩

private lemma setoid_ideal_injection_card
  (s : Setup_spo α):-- (q : Quotient s.setoid)  :
  #(filter (fun ss => (spo_closuresystem s).sets (Finset.image Subtype.val ss)) s.V.attach.powerset) =
  #(filter (fun s_1 => (spo_closuresystem s).sets s_1) (spo_closuresystem s).ground.powerset) :=
by
  let S₀ := s.V.attach.powerset
  let φ : Finset s.V → Finset α := fun ss => ss.image Subtype.val
  let S₁ := (spo_closuresystem s).ground.powerset
  let P := (spo_closuresystem s).sets

  change #(S₀.filter (fun s => P (φ s))) = #(S₁.filter P)

  let cfi := card_filter_image_eq S₀ φ P
  have : InjOn φ ↑(filter (fun x => P (φ x)) S₀) := by
    exact image_val_inj_on (filter (fun x => P (φ x)) S₀)
  specialize cfi this
  rw [cfi]

  have :s.V = (spo_closuresystem s).ground := by  dsimp [spo_closuresystem]
  have h_image : Finset.image φ S₀ = S₁ := by
    dsimp [S₀, S₁, φ]
    exact powerset_image_attach s.V

  dsimp [S₁]
  dsimp [S₀, φ, P]

  --simp_all only [coe_filter, Finset.mem_powerset, S₀, φ, S₁, P]
  simp_all only [coe_filter, Finset.mem_powerset, P, S₀, φ, S₁]

private lemma setoid_ideal_number_of_hyperedges (s : Setup_spo α)(q : Quotient s.setoid ):
  (setoid_ideal_injection_domain s q).card + (setoid_ideal_injection_codomain s q).card =
  (spo_closuresystem s).number_of_hyperedges := by
  dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain]
  dsimp [SetFamily.number_of_hyperedges]
  let A := fun (ss:Finset s.V) => (spo_closuresystem s).sets (ss.image Subtype.val)
  let p := fun ss => classOf s q ⊆ ss
  let powerset := s.V.attach.powerset

  have h_part :
    (powerset.filter (fun ss => A ss ∧ p ss)).card +
    (powerset.filter (fun ss => A ss ∧ ¬p ss)).card =
    (powerset.filter A).card := by
    exact Eq.symm (add_compl_card powerset A p)

  dsimp [A, p, powerset] at h_part
  simp at h_part
  norm_cast
  rw [h_part]
  let siic := setoid_ideal_injection_card s
  exact siic

--The assumption in this theorem is Setup_spo, but since it uses maximality in hm, it is essentially an assumption of spo2.
private lemma setoid_ideal_domain_codomain (s : Setup_spo α)(q : Quotient s.setoid ) (hm: isMaximal_spo s q) :
  (setoid_ideal_injection_domain s q).card ≤ (setoid_ideal_injection_codomain s q).card := by


  have : Function.Injective (setoid_ideal_injection s q hm) := by
    intro a b hab
    exact (setoid_ideal_injection_injective s q hm hab)

  let fcl :=  @Finset.card_le_card_of_injective _ _ (setoid_ideal_injection_domain s q) (setoid_ideal_injection_codomain s q) (setoid_ideal_injection s q hm)
  specialize fcl this
  simp_all only

private lemma degree_le_setoid_ideal_injection_domain_card
  (s : Setup_spo α) (q : Quotient s.setoid) (x : {x // x ∈ classOf s q}) :
  (spo_closuresystem s).degree ↑↑x  = #(setoid_ideal_injection_domain s q) :=
by
  dsimp [setoid_ideal_injection_domain]
  dsimp [SetFamily.degree]
  dsimp [classOf]
  simp
  have svg:s.V = (spo_closuresystem s).ground := by  dsimp [spo_closuresystem]
  rw [←svg]

  let domain := filter (fun s_1 => (spo_closuresystem s).sets s_1 ∧ ↑↑x ∈ s_1) (spo_closuresystem s).ground.powerset

  have equiv: ∀ ss:Finset α, ss ∈ domain ↔ (s.V.attach.filter (fun (t: {x//x ∈ s.V}) => t.val ∈ ss)) ∈ (setoid_ideal_injection_domain s q) ∧ ss ⊆ s.V := by

    intro ss
    dsimp [domain]
    dsimp [setoid_ideal_injection_domain]
    dsimp [classOf]
    apply Iff.intro
    · intro hss
      simp_all only [Finset.mem_filter, Finset.mem_powerset]
      obtain ⟨left, right⟩ := hss
      obtain ⟨left1, right⟩ := right
      have ssV: ss ⊆ s.V := by
        exact left
      have fslem:(Finset.image Subtype.val (filter (fun t => ↑t ∈ ss) s.V.attach)) = ss := by
        ext sss
        simp_all only [Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists, exists_and_left,
          exists_prop, exists_eq_right_right, and_iff_left_iff_imp, domain]
        intro a
        rw [←svg]
        simp_all only [domain]
        obtain ⟨val, property⟩ := x
        obtain ⟨val, property⟩ := val
        simp_all only
        exact left a
      constructor
      ·
        constructor
        · simp_all only [filter_subset, domain]
        · constructor
          · rw [fslem]
            exact left1
          · intro sss hss
            rw [Finset.mem_filter]
            rw [Finset.mem_filter] at hss
            constructor
            · exact mem_attach s.V sss
            · --Quotient.mk'' sss = q
              --↑↑x ∈ ss
              --x : { x // x ∈ classOf s q }
              let xp := x.property
              dsimp [classOf] at xp
              rw [Finset.mem_filter] at xp
              have sr:s.setoid.r x sss := by
                simp_all only [mem_attach, true_and, domain]
                subst hss
                simp_all only [Quotient.eq]
              have : x.val.val ∈ ss := by
                simp_all only [mem_attach, true_and, domain]
              let sce := spo_closuresystem_equiv s x.val sss sr left1
              simp_all only [mem_attach, true_and, domain, sce]

      · simp_all only [domain]
    · intro hss
      simp_all only [Finset.mem_filter, Finset.mem_powerset]
      obtain ⟨left, right⟩ := hss
      have ss_filter:Finset.image Subtype.val (filter (fun t => ↑t ∈ ss) s.V.attach) = ss := by
        ext sss
        simp_all only [Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists, exists_and_left,
          exists_prop, exists_eq_right_right, and_iff_left_iff_imp, domain]
        intro a
        rw [←svg]
        simp_all only [filter_subset, true_and, domain]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right_1⟩ := left
        obtain ⟨val, property⟩ := val
        exact right a


      constructor
      · --simp_all only [filter_subset, domain]
        exact trivial
      · constructor
        · simp_all only [filter_subset, domain]
        · obtain ⟨left, left1, right1⟩ := left
          show ↑↑x ∈ ss
          let xp := x.property
          dsimp [classOf] at xp
          rw [Finset.mem_filter] at xp
          have :(classOf s q).image Subtype.val ⊆ ss := by
            dsimp [classOf]
            intro xx hxx
            rw [Finset.mem_image] at hxx
            simp at hxx
            obtain ⟨hh, h⟩ := hxx
            have :⟨xx,hh⟩ ∈ filter (fun a => Quotient.mk'' a = q) s.V.attach := by
              subst h
              simp_all only [filter_subset, Quotient.eq, mem_attach, true_and, mem_filter]
              obtain ⟨val, property⟩ := x
              obtain ⟨val, property⟩ := val
              simp_all only
              rfl
            have :⟨xx,hh⟩ ∈ filter (fun t => ↑t ∈ ss) s.V.attach := by
              exact right1 this
            simp at this
            exact this
          simp_all only [filter_subset, mem_attach, true_and, domain]
          obtain ⟨val, property⟩ := x
          obtain ⟨val, property⟩ := val
          simp_all only
          subst xp
          simp_all only [Quotient.eq]
          apply this
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_prop, and_true]
          rename_i property_1
          exact property_1

  let i : ∀(a : Finset α), (ha : a ∈ domain) → Finset {x // x ∈ s.V} :=
    fun a ha => s.V.attach.filter (fun ss =>  ss.val ∈ a)

  have equiv2 : ∀ ss : Finset α,
  ss ∈ domain ↔ ∃ (h : ss ∈ domain), i ss h ∈ setoid_ideal_injection_domain s q
  := by
    intro ss
    constructor
    · intro hss
      use hss
      simp_all only [mem_filter, Finset.mem_powerset, domain, i]
      simp_all only [mem_filter, Finset.mem_powerset, domain]
    · rintro ⟨hss, hi⟩
      exact hss

  have H₁ : ∀ a ha, i a ha ∈ (setoid_ideal_injection_domain s q) := by
    intro a ha
    let ea := (equiv2 a).mp ha
    obtain ⟨h, ea⟩ := ea
    exact ea

  have H₂ : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ := by
    dsimp [i]
    intro a₁ ha₁ a₂ ha₂ h_eq
    dsimp [domain] at ha₁
    rw [Finset.mem_filter] at ha₁
    obtain ⟨ha11, ha12 , ha13⟩ := ha₁
    have a1inV:a₁ ⊆ s.V:=
    by
      dsimp [spo_closuresystem] at ha11
      rw [Finset.mem_powerset] at ha11
      exact ha11
    dsimp [domain] at ha₂
    rw [Finset.mem_filter] at ha₂
    obtain ⟨ha21, ha22 , ha23⟩ := ha₂
    have a2inV:a₂ ⊆ s.V:=
    by
      dsimp [spo_closuresystem] at ha21
      rw [Finset.mem_powerset] at ha21
      exact ha21
    ext ss
    constructor
    · intro h
      have : ⟨x, by simp [h]⟩ ∈ s.V.attach.filter (fun x => ↑x ∈ a₁) :=
      by
        rw [Finset.mem_filter]
        have xvv:x.val.val ∈ s.V := by
            exact coe_mem x.val

        constructor
        ·
          apply mem_attach s.V
        ·
          exact ha13

      have hss: ss ∈ s.V := by
        exact a1inV h
      have hss1: ⟨ss,hss⟩ ∈ s.V.attach.filter (fun x => ↑x ∈ a₁) := by
        rw [Finset.mem_filter]
        constructor
        · apply mem_attach s.V
        · exact h
      have hss2: ⟨ss, hss⟩ ∈ s.V.attach.filter (fun x => ↑x ∈ a₂) := by
        rw [h_eq] at hss1
        exact hss1
      rw [Finset.mem_filter] at hss2
      exact hss2.2

    · intro h
      have hss2: ⟨x, by simp [h]⟩ ∈ s.V.attach.filter (fun x => ↑x ∈ a₂) :=
      by
        rw [Finset.mem_filter]
        have xvv:x.val.val ∈ s.V := by
            exact coe_mem x.val
        constructor
        ·
          apply mem_attach s.V
        ·
          exact ha23
      have hss: ss ∈ s.V := by
        exact a2inV h
      have hss2: ⟨ss, hss⟩ ∈ s.V.attach.filter (fun x => ↑x ∈ a₂) := by
        rw [Finset.mem_filter]
        constructor
        · apply mem_attach s.V
        · exact h
      have hss1: ⟨ss, hss⟩ ∈ s.V.attach.filter (fun x => ↑x ∈ a₁) := by
        rw [←h_eq] at hss2
        exact hss2
      rw [Finset.mem_filter] at hss1
      exact hss1.2

  have H₃ : ∀ b ∈ (setoid_ideal_injection_domain s q), ∃ a ha, i a ha = b := by
    intro b hb
    use b.image Subtype.val
    have fsv: Finset.image Subtype.val b ∈ domain :=
    by
      dsimp [domain]
      dsimp [setoid_ideal_injection_domain] at hb
      rw [Finset.mem_filter] at hb
      rw [Finset.mem_filter]
      constructor
      · dsimp [spo_closuresystem]
        let hb1 := hb.1
        apply Finset.mem_powerset.mpr
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨x', hx', rfl⟩ := hx
        exact coe_mem x'
      · obtain ⟨hb1,hb2,hb3⟩ := hb
        constructor
        · exact hb2
        · dsimp [classOf]
          let xp := x.property
          exact Finset.mem_image_of_mem Subtype.val (hb3 xp)

    let ea := (equiv2 (b.image Subtype.val)).mpr
    have :(∃ (h : Finset.image Subtype.val b ∈ domain), i (Finset.image Subtype.val b) h ∈ setoid_ideal_injection_domain s q) :=
    by
      use fsv

      exact H₁ (Finset.image Subtype.val b) fsv
    specialize ea this
    use ea
    dsimp [i]
    simp
    have :i (Finset.image Subtype.val b) fsv = b := by
      dsimp [i]
      rw [Finset.mem_filter] at fsv
      simp
      ext y
      constructor
      · intro h
        rw [Finset.mem_filter] at h
        exact h.2
      · intro h
        rw [Finset.mem_filter]
        constructor
        · exact mem_attach s.V y
        · exact h
    dsimp [i] at this
    simp at this
    exact this
  exact Finset.card_bij i H₁ H₂ H₃

--Setup_spo2からSetup_spoに変更した。この定理自体はSetup_spoの仮定だが、hmで極大性の仮定を使うので、実質spo2。
private lemma setoid_ideal_rare (s : Setup_spo α)(q : Quotient s.setoid )(hm: isMaximal_spo s q) :
  ∀ (x : classOf s q), (spo_closuresystem s).toSetFamily.is_rare x := by

  dsimp [SetFamily.is_rare]
  rw [←setoid_ideal_number_of_hyperedges s q]
  let sid := setoid_ideal_domain_codomain s q hm

  intro x_1
  simp
  let dls := degree_le_setoid_ideal_injection_domain_card s q x_1
  linarith
-- If a certain equivalence class is size 2 or higher, the vertex becomes rare.
-- If the maximum element does not appear in singleton_if_not_maximal in spo2, the size is 1.
-- Therefore, equivalence classes of size 2 or higher will be rare vertex.
-- This lemma uses singleton_if_not_maximal, so the assumption must be Setup_spo2, not Setup_spo.
theorem spo2_rare (s : Setup_spo2 α) (q: Quotient s.setoid) (hx:(classOf s.toSetup_spo q).card ≥ 2) :
  ∀ (y : s.V), @Quotient.mk _ s.toSetup_spo.setoid y = q → (spo_closuresystem s.toSetup_spo).is_rare y :=
by
  intro y hq
  have hm: isMaximal_spo s.toSetup_spo q :=
  by
    exact s.singleton_if_not_maximal q hx
  let sir := setoid_ideal_rare s.toSetup_spo q hm
  have : y ∈ classOf s.toSetup_spo q := by
    subst hq
    simp_all only [ge_iff_le]
    obtain ⟨val, property⟩ := y
    simp [classOf]
    rfl

  specialize sir ⟨y,this⟩
  subst hq
  simp_all only [ge_iff_le]
