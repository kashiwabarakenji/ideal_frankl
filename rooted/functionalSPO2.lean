import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Quot
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

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

structure Setup_spo2 (α : Type) [Fintype α] [DecidableEq α]
  extends Setup_spo α where
  -- 極大でない要素の同値類のサイズが 1
  singleton_if_not_maximal :
  ∀ q : Quotient toSetup_spo.setoid,
    (classOf toSetup_spo q).card ≥ 2 →
    isMaximal_spo toSetup_spo q


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
    dsimp [isMaximal_spo] at hq
    let csm := eqClass_Maximal s q hq
    dsimp [isMaximalQ] at csm
    dsimp [isMaximal_spo]
    intro y h
    specialize csm y
    dsimp [setup_setupspo] at h
    dsimp [partialOrderOfFq] at h
    have : s.po.le q y := by
      simp_all only [ge_iff_le]
      exact reach_leq2 s q y h
    specialize csm this

    rw [spole_iff_po] at csm
    exact csm
}

lemma setup_trace_reach (s : Setup_spo α) (x: s.V) (hx:(classOf s (@Quotient.mk _ s.setoid x
)).card ≥ 2) (q1 q2 : Quotient (restrictedSetoid s x)) :
  reach (setup_trace_base s x hx).fq q1 q2 ↔
  reach s.fq (toOld s x q1) (toOld s x q2) :=
by
  dsimp [reach]
  constructor
  · intro h
    obtain ⟨n, h⟩ := h
    dsimp [setup_trace_base] at h
    use n
    let stf := setup2_trace_fq_n s x hx n
    simp at stf
    dsimp [setup_trace_base] at stf
    rw [stf] at h
    simp at h
    rw [←h]
    rw [NewOld_id s x]
  · intro h
    obtain ⟨n, h⟩ := h
    use n
    dsimp [setup_trace_base]
    let stf := setup2_trace_fq_n s x hx n
    simp at stf
    dsimp [setup_trace_base] at stf
    rw [stf]
    simp
    rw [h]
    exact OldNew_id s x hx q2

lemma setup_trace_noLoop (s : Setup_spo α) (x: s.V) (hx:(classOf s (@Quotient.mk _ s.setoid x
)).card ≥ 2) (q1 q2 : Quotient (restrictedSetoid s x)) :
  reach (fun q => toNew s x hx (s.fq (toOld s x q))) q1 q2 →
 reach (fun q => toNew s x hx (s.fq (toOld s x q))) q2 q1 →
  q1 = q2 :=
by
  intro h1 h2
  let str1 := setup_trace_reach s x hx q1 q2
  dsimp [setup_trace_base] at str1
  rw [str1] at h1
  let str2 := setup_trace_reach s x hx q2 q1
  dsimp [setup_trace_base] at str2
  rw [str2] at h2
  have : toOld s x q1 = toOld s x q2 := by
    exact s.noLoop (toOld s x q1) (toOld s x q2) h1 h2
  have : toNew s x hx (toOld s x q1) = toNew s x hx (toOld s x q2) := by
    congr 1
  rw [OldNew_id s x hx q1] at this
  rw [OldNew_id s x hx q2] at this
  exact this

noncomputable def setup_trace (s : Setup_spo α)(x: s.V) (hx:(classOf s (@Quotient.mk _ s.setoid x
)).card ≥ 2): Setup_spo α :=
{
  V := s.V.erase x,
  nonemp := (setup_trace_base s x hx).nonemp,
    setoid := restrictedSetoid s x
  fq := fun q => toNew s x hx (s.fq (toOld s x q))
  --s.V上には半順序が導入済み。s.V.erase x上にはこれから導入する。
  noLoop := by
    intro q1 q2
    intro h1 h2
    simp at h1 h2
    exact setup_trace_noLoop s x hx q1 q2 h1 h2

  --s.V上には半順序が導入済み。s.V.erase x上にはこれから導入する。
  spo := partialOrderOfFq (setup_trace_base s x hx).fq (by
      intro q1 q2
      intro h1 h2
      exact setup_trace_noLoop s x hx q1 q2 h1 h2
  )
  h_spo := by
    simp_all only
    obtain ⟨val, property⟩ := x
    simp_all only
    rfl
}

omit [Fintype α] in
lemma card_of_image_subset (V1 V2: Finset α) (A : Finset V1)(B:Finset V2)
  (h : A.image Subtype.val ⊆ B.image Subtype.val) :
  B.card ≥ A.card := by
  --haveI : DecidableEq (Subtype (· : α → Prop)) := inferInstance
  have : A.card = (A.image Subtype.val).card := by
    symm
    apply Finset.card_image_of_injective
    simp_all only [Subtype.val_injective]
  have : (A.image Subtype.val).card ≤ (B.image Subtype.val).card := by exact Finset.card_le_card h
  have : (B.image Subtype.val).card ≤ B.card := by exact card_image_le
  simp_all only [ge_iff_le]
  linarith

noncomputable def toNew_card (s : Setup_spo α) (x : {x : α // x ∈ s.V})
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

/- 使わなかったけど、証明には時間がかかったので、しばらく残す。
  have :∀ y : α, y ∈ (classOf s q).image Subtype.val → y ∈(classOf (setup_trace s x hx) (toNew s x hx q)).image Subtype.val ∨ y = x:= by
    intro y
    dsimp [classOf]
    intro h0
    by_cases hh: y = x
    case pos =>
      simp [hh]
    case neg =>
      simp [hh]
      constructor --yの行き先がqの行き先と同じことを示す。これはh0からいえる。
      · rw [Finset.mem_image] at h0
        obtain ⟨w, h0⟩ := h0
        rw [Finset.mem_filter] at h0
        simp at h0
        obtain ⟨h1,h2⟩ := h0
        simp_all
        rw [←h1]
        have hy : y ∈ s.V := by
          simp_all only [ge_iff_le, Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists,
            exists_and_right, exists_eq_right]
          obtain ⟨val, property⟩ := x
          simp_all only
          subst h2 h1
          simp_all only [Subtype.coe_eta, coe_mem, exists_const]

        --let tn := toErased_eq_ne s x ⟨y, hy⟩ hx
        have :⟨y, hy⟩ ≠ x := by
          simp_all only [Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists, exists_and_right,
            exists_eq_right, exists_true_left, ne_eq]
          subst h0
          obtain ⟨val, property⟩ := x
          simp_all only [Subtype.mk.injEq, not_false_eq_true]

        --specialize tn this
        dsimp [toNew]
        dsimp [setup_trace]
        simp
        dsimp [toErased]
        --let rmc := representativeNeSelf_mem_classOf s x hx
        simp
        have : w ≠ x := by
          subst h1 h2
          simp_all only [Subtype.coe_eta, Quotient.eq, Finset.mem_image, mem_filter, mem_attach, true_and,
            Subtype.exists, exists_and_right, exists_eq_right, exists_const, ne_eq, not_false_eq_true]
        split
        · contradiction
        · --show (restrictedSetoid s x) ⟨y, ⋯⟩ ⟨↑w, ⋯⟩
          dsimp [restrictedSetoid]
          simp_all
          apply Quotient.eq''.mp
          apply  congrFun rfl
          intro hh
          simp_all only [Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists, exists_and_right,
            exists_eq_right]
          obtain ⟨val, property⟩ := x
          simp_all only
          obtain ⟨w, h_1⟩ := h0
          subst h_1
          rw [setup_trace]
          simp_all only [mem_erase, ne_eq, not_false_eq_true, and_self]
-/

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

noncomputable def setup_trace_spo2 (s : Setup_spo2 α)(x: s.V) (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x
)).card ≥ 2): Setup_spo2 α :=
{
  V := s.V.erase x
  nonemp := (setup_trace_base s.toSetup_spo  x hx).nonemp,
  fq := fun q => toNew s.toSetup_spo  x hx (s.fq (toOld s.toSetup_spo x q))
  noLoop := by
    intro q1 q2
    intro h1 h2
    simp at h1 h2
    exact setup_trace_noLoop s.toSetup_spo x hx q1 q2 h1 h2
  setoid := restrictedSetoid s.toSetup_spo x
  spo := partialOrderOfFq (setup_trace_base s.toSetup_spo x hx).fq (by
      intro q1 q2
      intro h1 h2
      exact setup_trace_noLoop s.toSetup_spo  x hx q1 q2 h1 h2
  )
  h_spo := by
    simp_all only
    obtain ⟨val, property⟩ := x
    simp_all only
    rfl
  singleton_if_not_maximal := by
    intro q hq
    dsimp [isMaximal_spo] at hq
    simp
    simp at q
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

    --hqの条件より、あたらしい世界での同値類の大きさは2以上。条件hx。
    --ということは、古い世界ではそれよりも小さくなることはないので、同値類の大きさは2以上。
    --s.singleton_if_not_maximal q hqを利用する必要あり。
    --ということは、古い世界では極大元。
    --古い世界と新しい世界の大小関係は一致しているので、新しい世界でも極大元。}

}
