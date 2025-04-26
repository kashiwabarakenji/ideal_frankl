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

--Setup_spoよりも仮定としてはつよくなっている。大きさ2以上の同値類が極大なもののみ。
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

--新しく写って同値類が大きくなることはない。
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
lemma toErased_eq_lem (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (y z: {y : α // y ∈ s.V}) (hx:(classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2)
   (ree: restrictedSetoid s x (toErased s x hx y) (toErased s x hx z)) :
   s.setoid.r y z :=
by
  dsimp [restrictedSetoid] at ree
  dsimp [toErased] at ree
  by_cases hy: y = x
  case pos =>
    simp_all only [Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists, exists_and_right,
      exists_eq_right, exists_true_left]
    by_cases hz: z = x
    case pos =>
      subst hz
      subst hy
      simp_all only [↓reduceDIte, Subtype.coe_eta]
      simp_all only
      obtain ⟨val, property⟩ := y
      simp_all only
      rfl
    case neg =>
      simp at ree
      subst hy
      simp [dif_neg hz] at ree
      set rnsm := representativeNeSelf_mem_classOf s y hx
      have : s.setoid.r (representativeNeSelf2 s y hx) z := by
        dsimp [toErased]
        simp_all only [Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists, exists_and_right,
          exists_eq_right, exists_true_left]
        obtain ⟨val, property⟩ := y
        obtain ⟨val_1, property_1⟩ := z
        simp_all only
        exact ree
      have : s.setoid.r (representativeNeSelf2 s y hx) y := by
        exact representativeNeSelf_mem_classOf3 s y hx
      exact Setoid.trans' s.setoid (id (Setoid.symm' s.setoid this)) ree
  case neg =>
    by_cases hz: z = x
    case pos =>
      --subst hz
      simp at ree
      simp [dif_neg hy] at ree
      set rnsm := representativeNeSelf_mem_classOf3 s x hx
      rw [hz]
      simp [dif_pos hz] at ree

      have : s.setoid.r (representativeNeSelf2 s x hx) y := by
        apply id (Setoid.symm' )
        subst hz
        obtain ⟨val, property⟩ := y
        obtain ⟨val_1, property_1⟩ := z
        simp_all only
        exact ree

      have : s.setoid.r (representativeNeSelf2 s x hx) x := by
        exact representativeNeSelf_mem_classOf3 s x hx
      exact Setoid.trans' s.setoid ree rnsm

    case neg =>
      simp_all only [↓reduceDIte]
      simp_all only [ge_iff_le, not_false_eq_true]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      obtain ⟨val_2, property_2⟩ := z
      simp_all only
      exact ree

--xと違う同値類は、恒等写像。excessの議論で使う。
lemma toNew_card_eq (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (q: Quotient s.setoid)
   (hx:(classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2)
   (nq:  q ≠ @Quotient.mk _ s.setoid x) :
  (classOf s q).image Subtype.val = (classOf (setup_trace s x hx) (toNew s x hx q)).image Subtype.val :=
by
  ext y

  dsimp [setup_trace]
  constructor
  · intro h
    simp at h
    obtain ⟨w, h⟩ := h
    rw [Finset.mem_image]
    dsimp [classOf]
    simp
    dsimp [classOf] at h
    simp at h
    have yinsV:y ∈ s.V :=
    by
      simp_all only
    have ynotx:¬y = x.val  := by
      by_contra h_contra
      have :x = ⟨y, yinsV⟩ := by
        simp_all only [Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists, exists_and_right,
          exists_eq_right, exists_true_left]
      rw [this] at nq
      rw [←h] at nq
      contradiction
    have : ¬y = ↑x ∧ y ∈ s.V := by
      constructor
      · exact ynotx
      · exact yinsV
    use this
    dsimp [toNew ]
    subst h
    simp_all only [not_false_eq_true, ne_eq, Quotient.eq, Quotient.lift_mk]
    obtain ⟨val, property⟩ := x
    obtain ⟨left, right⟩ := this
    simp_all only
    dsimp [toErased]
    simp_all only [Subtype.mk.injEq, ↓reduceDIte]
    simp_all only [ge_iff_le]
    rfl

  · intro h
    rw [Finset.mem_image] at h
    rw [Finset.mem_image]
    obtain ⟨w, h⟩ := h
    have winsV:w.val ∈ s.V :=
    by
      let wp := w.property
      rw [Finset.mem_erase] at wp
      exact wp.2
    use ⟨w.val, winsV⟩
    dsimp [classOf] at h
    constructor
    · dsimp [classOf]
      rw [Finset.mem_filter]
      constructor
      · simp_all only [ne_eq, mem_filter, mem_attach, true_and]
      · rw [Finset.mem_filter] at h
        obtain ⟨⟨h1, h2⟩, h⟩ := h

        have yinsV:y ∈ s.V :=
        by
          subst h
          simp_all only [ne_eq, mem_attach]
        have ynotx:¬y = x.val  := by
          by_contra h_contra
          have :x = ⟨y, yinsV⟩ := by
            simp_all only [Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists, exists_and_right,
              exists_eq_right, exists_true_left]
          /-
          rw [this] at nq
          --xとyが同じであれば、yはtoNewで、恒等写像ではない。
          --hでwとyが同じであり、h2で、qとwが同じところに移るのに、nqで等しくないといっているので矛盾
          have nq': q ≠ @Quotient.mk _ s.setoid ⟨y, yinsV⟩ := by
            exact nq
          have hqq: @Quotient.mk _ s.setoid ⟨w.val, winsV⟩ = @Quotient.mk _ s.setoid ⟨y, yinsV⟩ := by
            cases h
            exact rfl
          have : q ≠ @Quotient.mk _ s.setoid ⟨w.val, winsV⟩ := by
            exact Ne.symm (ne_of_eq_of_ne hqq (id (Ne.symm nq)))
          -/
          have : w.val = x.val := by
            subst h
            exact h_contra
          let wp := w.property
          rw [Finset.mem_erase] at wp
          let wp1 := wp.1
          contradiction
        let teen := toErased_eq_ne s x ⟨y, yinsV⟩ hx
        have :⟨y, yinsV⟩ ≠ x := by
          subst h
          simp_all only [ne_eq, mem_attach]
          obtain ⟨val, property⟩ := x
          obtain ⟨val_1, property_1⟩ := w
          simp_all only [Subtype.mk.injEq, not_false_eq_true]
        specialize teen this
        dsimp [toNew]  at h2
        --h2は新しい制限された世界での式。証明すべきは、制限されない世界。
        --しかし、teenによると、この対応は恒等写像。hによるとwとyは同じ。
        let  teenw := toErased_eq_ne s x ⟨w, winsV⟩ hx
        have :⟨w, winsV⟩ ≠ x := by
          subst h
          simp_all only [ne_eq, mem_attach]
          obtain ⟨val, property⟩ := x
          obtain ⟨val_1, property_1⟩ := w
          simp_all only [Subtype.mk.injEq, not_false_eq_true]
        specialize teenw this
        obtain ⟨z, rfl⟩ := Quot.exists_rep q
        simp at h2
        have : (restrictedSetoid s x) (toErased s x hx ⟨w.val,winsV⟩) (toErased s x hx z) :=
        by
          subst h
          simp_all only [mem_attach, Subtype.coe_eta, ne_eq]

        let tel := toErased_eq_lem s x ⟨w.val,winsV⟩ z hx this
        have : @Quotient.mk _ s.setoid ⟨↑w, winsV⟩ = @Quotient.mk _ s.setoid z :=
        by
          subst h
          simp_all only [mem_attach, Subtype.coe_eta, ne_eq, Quotient.eq, tel]
        subst h
        simp_all only [mem_attach, Subtype.coe_eta, ne_eq, Quotient.eq, tel]
        simp_all only [ne_eq, not_false_eq_true]
        exact Quotient.sound tel

    · simp_all only [ne_eq, mem_filter, mem_attach, true_and]

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

--xに関わらない同値類の場合は、cardの大きさは変わらない。
lemma toNew_classOf (s : Setup_spo2 α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2)
  (cls : Quotient s.setoid) :
   cls ≠ (@Quotient.mk _ s.setoid x) →
    (classOf s.toSetup_spo cls).card  = (classOf (setup_trace_spo2 s x hx).toSetup_spo (toNew s.toSetup_spo x hx cls)).card :=
by
  intro h
  dsimp [setup_trace_spo2]
  dsimp [toNew]
  dsimp [classOf]
  --bij_cardで証明するのがいいか。
  let tce := toNew_card_eq s.toSetup_spo x cls hx h
  --tceと、ゴールの関係を探る。

  let src := filter (fun a : {y // y ∈ s.V} => Quotient.mk'' a = cls) s.V.attach
  let tgt := filter (fun a : {y // y ∈ s.V.erase x} =>
      Quotient.mk'' a = cls.liftOn (fun z => ⟦toErased s.toSetup_spo x hx z⟧)
        (by
          intro a b hab
          show Quotient.mk'' (toErased s.toSetup_spo x hx a) = Quotient.mk'' (toErased s.toSetup_spo x hx b)
          have : s.setoid.r a b :=
          by
            exact hab
          let tee := toErased_eq s.toSetup_spo x a b hx
          apply tee
          simp_all only [ne_eq, Quotient.eq]
        )
    ) (s.V.erase x).attach
  --tgtの定義の仕方はこれでよかったのか。toNewとclassOfで定義する方法もあったと思う。
  have tgt_classOf : tgt = classOf (setup_trace_spo2 s x hx).toSetup_spo (toNew s.toSetup_spo x hx cls) := by
    dsimp [tgt]
    dsimp [classOf]
    dsimp [setup_trace_spo2]
    dsimp [toNew]

  have xnotinsrc: x ∉ src := by
    intro h
    dsimp [src] at h
    simp at h
    obtain ⟨val, property⟩ := x
    simp_all only [mem_attach, mem_filter, not_true_eq_false, src]
    rename_i h_1
    subst h
    simp_all only [Quotient.lift_mk, Quotient.eq, tgt]
    apply h_1
    simp_all only

  have xnotintgt: x.val ∉ tgt.image Subtype.val := by
    intro h
    dsimp [tgt] at h
    simp at h

  --これを証明すれば、定理の証明が終わる。
  have : src.image Subtype.val = tgt.image Subtype.val := by
    dsimp [src]
    --dsimp [tgt]  -- tgt_classOfを使うてもある。
    rw [tgt_classOf]
    ext y
    constructor
    · intro h
      rw [Finset.mem_image] at h
      rw [Finset.mem_image]
      simp at h
      obtain ⟨w, h⟩ := h
      simp
      have : ¬y = x.val ∧ y ∈ s.V := by
        constructor
        · intro h_contra
          subst h h_contra
          simp_all only [Subtype.coe_eta, Quotient.lift_mk, Quotient.eq, mem_filter, mem_attach, true_and,
            Finset.mem_image, Subtype.exists, mem_erase, ne_eq, exists_and_right, exists_eq_right, not_true_eq_false,
            and_true, IsEmpty.exists_iff, not_false_eq_true, tgt, src]
          obtain ⟨val, property⟩ := x
          simp_all only
          contradiction
        · exact w
      use this
      --have : (restrictedSetoid s.toSetup_spo x).r
      have yinsVe:y ∈ (setup_trace_spo2 s x hx).V := by
        dsimp [setup_trace_spo2]
        simp_all only [mem_erase, ne_eq, not_false_eq_true, and_self]
      let cq := (classOf_quotient  (setup_trace_spo2 s x hx).toSetup_spo ⟨y,yinsVe⟩ (toNew s.toSetup_spo x hx cls)).mp
      apply cq
      --h:Quotient.mk'' ⟨y, ⋯⟩ = clsを使って証明。
      have : toNew s.toSetup_spo x hx (@Quotient.mk _ s.setoid ⟨y,w⟩) = @Quotient.mk _ (restrictedSetoid s.toSetup_spo x) ⟨y, yinsVe⟩ := by
        dsimp [toNew]
        dsimp [restrictedSetoid]

        simp_all only [mem_erase, ne_eq, not_false_eq_true, and_self]
        dsimp [toErased]
        split
        · let rnsm := representativeNeSelf_mem_classOf s.toSetup_spo x hx
          rename_i h_2
          subst h h_2
          simp_all only [not_true_eq_false, and_true]
        ·
          subst h
          simp_all only [and_true, Quotient.lift_mk, Quotient.eq, mem_filter, mem_attach, true_and, Finset.mem_image,
            Subtype.exists, mem_erase, ne_eq, exists_and_right, exists_eq_right, not_true_eq_false, coe_mem,
            IsEmpty.exists_iff, not_false_eq_true, tgt, src]
      subst h
      simp_all only [and_true, Quotient.lift_mk, Quotient.eq, mem_filter, mem_attach, true_and, Finset.mem_image,
        Subtype.exists, mem_erase, ne_eq, exists_and_right, exists_eq_right, not_true_eq_false, coe_mem,
        IsEmpty.exists_iff, not_false_eq_true, tgt, src]
      obtain ⟨val, property⟩ := x
      simp_all only
      rfl

    · intro h

      simp at h
      obtain ⟨w, h⟩ := h
      rw [Finset.mem_image]
      simp
      use w.2
      have yinsVe:y ∈ (setup_trace_spo2 s x hx).V := by
        dsimp [setup_trace_spo2]
        simp_all only [mem_erase, ne_eq, not_false_eq_true, and_self]
      let cq := (classOf_quotient (setup_trace_spo2 s x hx).toSetup_spo ⟨y, yinsVe⟩ (toNew s.toSetup_spo x hx cls)).mpr
      have tnqlem: toNew s.toSetup_spo x hx (@Quotient.mk _ s.setoid ⟨y,w.2⟩) = @Quotient.mk _ (restrictedSetoid s.toSetup_spo x) ⟨y, yinsVe⟩ := by
        dsimp [toNew]
        dsimp [restrictedSetoid]
        simp_all only [mem_erase, ne_eq, not_false_eq_true, and_self]
        dsimp [toErased]
        split
        · let rnsm := representativeNeSelf_mem_classOf s.toSetup_spo x hx
          rename_i h_2
          simp_all only [mem_filter, mem_attach, true_and, Finset.mem_image, Subtype.exists, mem_erase, ne_eq,
            exists_and_right, exists_eq_right, not_true_eq_false, coe_mem, and_true, IsEmpty.exists_iff,
            not_false_eq_true, Subtype.coe_eta, Quotient.eq, tgt, src]
          obtain ⟨val, property⟩ := x
          obtain ⟨left, right⟩ := w
          simp_all only [Subtype.mk.injEq, src]
        ·
          simp_all only [mem_filter, mem_attach, true_and, Finset.mem_image, Subtype.exists, mem_erase, ne_eq,
            exists_and_right, exists_eq_right, not_true_eq_false, coe_mem, and_true, IsEmpty.exists_iff,
            not_false_eq_true, tgt, src]
      have yinco:⟨y, yinsVe⟩ ∈ classOf (setup_trace_spo2 s x hx).toSetup_spo (toNew s.toSetup_spo x hx cls) :=
      by
        simp_all only [mem_filter, mem_attach, true_and, Finset.mem_image, Subtype.exists, mem_erase, ne_eq,
          exists_and_right, exists_eq_right, not_true_eq_false, coe_mem, and_true, IsEmpty.exists_iff,
          not_false_eq_true, tgt, src]
      specialize cq yinco
      have :toNew s.toSetup_spo x hx (@Quotient.mk _ s.setoid ⟨y,w.2⟩) = toNew s.toSetup_spo x hx cls :=
      by
        simp_all only [mem_filter, mem_attach, true_and, Finset.mem_image, Subtype.exists, mem_erase, ne_eq,
          exists_and_right, exists_eq_right, not_true_eq_false, coe_mem, and_true, IsEmpty.exists_iff,
          not_false_eq_true, tgt, src]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := w
        simp_all only [src]
        rfl
      let ca := congrArg (toOld s.toSetup_spo x ) this
      rw [NewOld_id s.toSetup_spo x hx] at ca
      rw [NewOld_id s.toSetup_spo x hx] at ca
      exact ca

  have : src.card = tgt.card := by
    --dsimp [src]
    --dsimp [tgt]
    -- Subtype.val は injective なので
    have h_inj_src : Set.InjOn Subtype.val src.toSet := by
      intros a _ b _ hab
      exact Subtype.ext hab

    have h_inj_tgt : Set.InjOn Subtype.val tgt.toSet := by
      intros a _ b _ hab
      exact Subtype.ext hab

    -- それぞれに card_image_iff を適用
    have h_card_src : (Finset.image Subtype.val src).card = src.card :=
      (Finset.card_image_iff.mpr h_inj_src)

    have h_card_tgt : (Finset.image Subtype.val tgt).card = tgt.card :=
      (Finset.card_image_iff.mpr h_inj_tgt)

    -- そして this を使って等式を連結
    have : src.card = tgt.card := by
      rw [←h_card_src, this, h_card_tgt]

    exact this

  simp_all only [mem_filter, mem_attach, true_and, Finset.mem_image, Subtype.exists, mem_erase, ne_eq, exists_and_right,
    exists_eq_right, not_true_eq_false, coe_mem, and_true, IsEmpty.exists_iff, not_false_eq_true, tgt, src]
