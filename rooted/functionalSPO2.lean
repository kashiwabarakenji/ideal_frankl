import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Quot
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
import rooted.functionalSPOTrace

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

--Setup_spo2 is the premise from here.
--Some of the stories include the premise of Setup_spo, but this is a story that leads to setup_spo2.
--trace also includes stories that lead to maximal.

--As a more assumption than Setup_spo, it's stronger.The assumption is added that only the maximum equivalent class of size 2 or higher is the maximum.
structure Setup_spo2 (α : Type) [Fintype α] [DecidableEq α]
  extends Setup_spo α where
  singleton_if_not_maximal :
  ∀ q : Quotient toSetup_spo.setoid,
    (classOf toSetup_spo q).card ≥ 2 →
    isMaximal_spo toSetup_spo q

--This is where we talk about maximity.The story of the maximity is not SPO, but SPO 2, so I moved it.
--But in terms of the strength of the assumption, it might have been better to have been in the SPO.Shall we move again?
-- The relationship between the maximity of Setup_spo and the maximity of Setup2.This is not used.
lemma isMaximal_spo_iff (s: Setup2 α) (q : Quotient s.setoid) :
  isMaximal_spo (setup_setupspo s) q ↔
  isMaximalQ s q :=
by
  dsimp [isMaximal_spo]
  dsimp [isMaximalQ]
  dsimp [setup_setupspo]
  apply Iff.intro
  · intro h
    intro y
    let hy := h y
    rw [spole_iff_po]
    rw [spole_iff_po]
    exact hy
  · intro h
    intro y
    let hy := h y
    rw [spole_iff_po] at hy
    rw [spole_iff_po] at hy
    exact hy

--If the magnitude of the equivalence class is 2 or more, the maximum value class is valid.
--Used with setup2_induces_spo.
theorem eqClass_Maximal (s: Setup2 α) (q : Quotient s.setoid) :
  (classOf (setup_setupspo s) q).card ≥ 2 → isMaximalQ s q  := by
  intro h
  rw [←eqClass_Class_of2] at h
  dsimp [isMaximalQ]
  let ecs := eqClass_size_ge_two_implies_inverse s.toSetup (Quotient.out q) h
  obtain ⟨x, hx⟩ := Quotient.exists_rep q
  intro q2
  obtain ⟨y, hy⟩ := Quotient.exists_rep q2
  specialize ecs y
  let imi := isMaximal_iff s x
  rw [hx] at imi
  dsimp [isMaximal] at imi
  dsimp [isMaximalQ] at imi
  have: @Quotient.mk _ s.setoid q.out = q := by
    subst hy hx
    simp_all only [ge_iff_le, Subtype.forall, Quotient.out_eq]
  rw [←this]
  have : x ∈ eqClass_setup s.toSetup q.out := by
      dsimp [eqClass_setup]
      rw [Finset.mem_filter]
      constructor
      ·
        subst hy hx
        simp_all only [ge_iff_le, Subtype.forall, Quotient.out_eq, mem_attach]
      ·
        dsimp [eqClass_setup]
        rw [←hx]
        exact Quotient.mk_out x
  have q_eq : s.pre.le x q.out := by
    exact eqClass_ge s.toSetup q.out x this
  have q_eq2 : s.pre.le q.out x := by
    exact eqClass_le s.toSetup q.out x this
  rw [←hy]
  let imimp := imi.mp
  have : ∀ (b : { x // x ∈ s.V }), x ≤ b → b ≤ x := by
    intro b h
    have : q.out ≤ b := by
      exact Preorder.le_trans q.out x b q_eq2 h
    have : b ≤ q.out := by
      apply eqClass_size_ge_two_implies_inverse s.toSetup q.out
      subst hy hx
      simp_all only [ge_iff_le, Quotient.out_eq]
      subst hy hx
      simp_all only [ge_iff_le, Quotient.out_eq]
    exact Preorder.le_trans b q.out x this q_eq2
  specialize imimp this
  intro a
  subst hy hx
  simp_all only [Subtype.forall, ge_iff_le, Subtype.coe_eta, implies_true, Quotient.out_eq]


--Embedded from Setup2 to Setup_spo2.
--Used in functionalMain's principal theorem average_rare.
--Here, except for the maximum element, it proves that the size of the equivalence class is 1.
def setup2_induces_spo (s : Setup2 α) : Setup_spo2 α :=
{
  V := s.V,
  nonemp := s.nonemp,
  setoid := s.setoid,
  fq := fq s
  noLoop := (setup_setupspo s).noLoop,
  spo := (setup_setupspo s).spo,
  h_spo := (setup_setupspo s).h_spo,
  singleton_if_not_maximal := by
    intro q hq
    let csm := eqClass_Maximal s q hq
    dsimp [isMaximalQ] at csm
    dsimp [isMaximal_spo]
    intro y h
    specialize csm y
    dsimp [setup_setupspo] at h
    dsimp [partialOrderOfFq] at h
    have : s.po.le q y := by
      simp_all only [ge_iff_le]
      exact reach_po_leq s q y h
    specialize csm this

    rw [spole_iff_po] at csm
    exact csm
}

-----------------------
--trace definitions and lemma.
--Related to Setup_spo2
------------------------------

--Use right below.
omit [Fintype α] in
private lemma card_of_image_subset (V1 V2: Finset α) (A : Finset V1)(B:Finset V2)
  (h : A.image Subtype.val ⊆ B.image Subtype.val) :
  B.card ≥ A.card := by
  have : A.card = (A.image Subtype.val).card := by
    symm
    apply Finset.card_image_of_injective
    simp_all only [Subtype.val_injective]
  have : (A.image Subtype.val).card ≤ (B.image Subtype.val).card := by exact Finset.card_le_card h
  have : (B.image Subtype.val).card ≤ B.card := by exact card_image_le
  simp_all only [ge_iff_le]
  linarith

--The equivalent class will not increase when a new photo is taken.The premise is Setup_spo, but it is used within setup_trace_spo2.
private lemma toNew_card (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (q: Quotient s.setoid)
   (hx:(classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2):
  (classOf s q).card ≥ (classOf (setup_trace s x hx) (toNew s x hx q)).card :=
by
  have :(classOf (setup_trace s x hx) (toNew s x hx q)).image Subtype.val ⊆ (classOf s q).image Subtype.val :=
  by
    intro y
    intro h
    dsimp [setup_trace] at h
    simp at h
    obtain ⟨w, h⟩ := h
    rw [Finset.mem_image]
    dsimp [classOf]
    simp
    dsimp [classOf] at h
    simp at h
    have :y ∈ s.V :=
    by
      simp_all only
    use this
    let fh := congrArg (toOld s x) h
    rw [NewOld_id s x hx] at fh
    rw [←fh]
    dsimp [toOld]
  let cl := classOf s q

  exact card_of_image_subset (setup_trace s x hx).V s.V (classOf (setup_trace s x hx) (toNew s x hx q)) (classOf s q) this

--Setup_spo2 is not a premise, but it is also used to prove the setup_trace_spo2 file below.That's the premise of SPO2.
--trace does not change the size of the size.
--There is room for moving the location to SPOTrace, but it is here as it is a lemma of the theorem assumption based on spo2.
--Is the difference between writing the relationship with setup_trace_reach with reach or spo.le?It is used in both directions of this proof.
lemma setup_trace_spo_le (s : Setup_spo α) (x: s.V) (hx:(classOf s (@Quotient.mk _ s.setoid x
)).card ≥ 2) (q1 q2 : Quotient (restrictedSetoid s x)) :
  (setup_trace s x hx).spo.le q1 q2 ↔ s.spo.le (toOld s x q1) (toOld s x q2) :=
by
  dsimp [setup_trace]
  rw [s.h_spo]
  constructor
  · intro h
    let rl := reach_leq s (toOld s x q1) (toOld s x q2)
    have : reach (setup_trace s x hx).fq q1 q2 := by
      obtain ⟨val, property⟩ := x
      simp_all only
      exact h
    have : reach s.fq (toOld s x q1) (toOld s x q2) := by
      exact (setup_trace_reach s x hx q1 q2).mp this
    simp_all only [ge_iff_le]
    obtain ⟨val, property⟩ := x
    simp_all only
    exact this
  · intro h
    let rlv := reach_leq_rev s (toOld s x q1) (toOld s x q2)
    have :s.spo.le (toOld s x q1) (toOld s x q2) := by
      exact reach_leq s (toOld s x q1) (toOld s x q2) h
    specialize rlv this
    have : reach (setup_trace s x hx).fq q1 q2 := by
      apply (setup_trace_reach s x hx q1 q2).mpr
      simp_all only [ge_iff_le]
    simp_all only [ge_iff_le]
    obtain ⟨val, property⟩ := x
    simp_all only
    exact this

--Unlike setup2_induces_spo, it takes a trace.However, it is assumed that SPO2.
--The definition of setup_trace, which was used in quite a variety of places, has been changed to that.It is used in Main.
--Setup_spo2 is required only if the condition is that only the maximum equivalent class of 2 or higher is required.
noncomputable def setup_trace_spo2 (s : Setup_spo2 α)(x: s.V) (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x
)).card ≥ 2): Setup_spo2 α :=
{
  V := s.V.erase x
  nonemp := (setup_trace_base s.toSetup_spo  x hx).nonemp,
  fq := fun q => toNew s.toSetup_spo  x hx (s.fq (toOld s.toSetup_spo x q))
  noLoop := by
    intro q1 q2
    intro h1 h2
    exact setup_trace_noLoop s.toSetup_spo x hx q1 q2 h1 h2
  setoid := restrictedSetoid s.toSetup_spo x
  spo := partialOrderOfFq (setup_trace_base s.toSetup_spo x hx).fq (by
      intro q1 q2
      intro h1 h2
      exact setup_trace_noLoop s.toSetup_spo  x hx q1 q2 h1 h2
  )
  h_spo := by
    obtain ⟨val, property⟩ := x
    simp_all only
    rfl
  singleton_if_not_maximal := by
    intro q hq
    simp at hq
    set q' := toOld s.toSetup_spo x q with hq'
    have thisq:q = toNew s.toSetup_spo x hx q' := by
      rw [hq']
      rw [OldNew_id s.toSetup_spo x hx]
    have ineq: (classOf s.toSetup_spo q').card ≥ (classOf (setup_trace s.toSetup_spo x hx) (toNew s.toSetup_spo x hx q')).card := by
      exact toNew_card s.toSetup_spo x q' hx
    have :(classOf (setup_trace s.toSetup_spo x hx) (toNew s.toSetup_spo x hx q')).card ≥ 2 := by
      rw [←thisq]
      exact hq
    have geq2: (classOf s.toSetup_spo q').card ≥ 2 := by
      exact Nat.le_trans this ineq
    have : isMaximal_spo s.toSetup_spo q' := by
      let ss := s.singleton_if_not_maximal q'
      exact ss geq2
    dsimp [isMaximal_spo]
    dsimp [isMaximal_spo] at this
    intro qq
    set qq' := (toOld s.toSetup_spo x) qq with hqq'
    intro hqq
    have : s.spo.le q' qq' := by
      exact (setup_trace_spo_le s.toSetup_spo x hx q qq).mp hqq
    have : s.spo.le qq' q' := by
      apply s.singleton_if_not_maximal q' geq2
      exact this

    have : (setup_trace s.toSetup_spo x hx).spo.le qq q := by
       apply (setup_trace_spo_le s.toSetup_spo x hx qq q).mpr
       rw [hq'] at this
       rw [hqq'] at this
       exact this
    exact this
}

--To clarify the position of setup_trace_spo2.Used in Main.
lemma setup_trace_spo2_lem (s : Setup_spo2 α)(x: s.V) (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2):
  (setup_trace_spo2 s x hx).toSetup_spo = setup_trace s.toSetup_spo x hx := by
  dsimp [setup_trace_spo2]
  dsimp [setup_trace]
