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
import rooted.functionalSPO

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

--This file is a lemma for the one-point limit trace, assuming Setup_spo.
--In the set family of the entire idea obtained from Setup_spo, if the equivalence class is 2 or more, even if the 1-trace is 1-trace, it will become Setup_spo again.setup_trace

--------------------------------------------------------------------------------------------------------------------------------
-- It is used in a variety of places.Setoid after trace.
def restrictedSetoid (s: Setup_spo α)(x : {x : α // x ∈ s.V}): Setoid {y : α // y ∈ s.V.erase x.val} :=
  Setoid.comap
    (fun y => ⟨y.val, Finset.mem_of_mem_erase y.property⟩)
    s.setoid



-- Takes one element from the same equivalent class as x.
noncomputable def representativeNeSelf
  (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s ⟦x⟧).card ≥ 2) :
    { y // y ∈ s.V.erase ↑x } :=
  have h' : ∃ b ∈ classOf s ⟦x⟧, b ≠ x := exists_ne_of_one_lt_card hx x
  let b := Classical.choose (exists_ne_of_one_lt_card hx x)
  have hb := Classical.choose_spec (exists_ne_of_one_lt_card hx x)
  ⟨b, by
    simp only [Finset.mem_erase]
    exact ⟨Subtype.coe_ne_coe.mpr hb.right, b.property⟩⟩

--The area to be extracted above is s.V.It is used.
noncomputable def representativeNeSelf2
  (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s ⟦x⟧).card ≥ 2) :
    { y // y ∈ s.V } :=
  ⟨
    (representativeNeSelf s x hx).val, by
    obtain ⟨val, property⟩ := x
    simp_all only
    simp [representativeNeSelf]⟩

-- Guaranteed that what you extracted is in the same value.
--It is also used by TraceIdeal.
lemma representativeNeSelf_mem_classOf
  (s : Setup_spo α) (x : {x // x ∈ s.V}) (hx : 2 ≤ (classOf s ⟦x⟧).card) :
  ⟨(representativeNeSelf s x hx).val, Finset.mem_of_mem_erase (representativeNeSelf s x hx).property⟩ ∈ (classOf s (@Quotient.mk _ s.setoid x)).erase x :=
by
  dsimp [representativeNeSelf]
  have hb := Classical.choose_spec (exists_ne_of_one_lt_card hx x)
  simp_all only [ne_eq, Subtype.coe_eta, mem_erase, not_false_eq_true, and_self]

--It is the same as above, but the expression is equivalent using setoid.r.
--It is also used by TraceIdeal.
lemma representativeNeSelf_mem_classOf2
  (s : Setup_spo α) (x : {x // x ∈ s.V}) (hx : 2 ≤ (classOf s ⟦x⟧).card) :
  s.setoid.r ⟨(representativeNeSelf s x hx), by
  obtain ⟨val, property⟩ := x
  simp_all only
  simp [representativeNeSelf]⟩ x :=
by
  dsimp [representativeNeSelf]
  have hb := Classical.choose_spec (exists_ne_of_one_lt_card hx x)
  simp_all only [ne_eq, Subtype.coe_eta, mem_erase, not_false_eq_true, and_self]
  dsimp [classOf] at hb
  rw [Finset.mem_filter] at hb
  obtain ⟨h1,h2⟩ := hb
  obtain ⟨h11,h12⟩ := h1
  exact Quotient.eq''.mp h12

--The only difference is that this is also equivalent.
--It is also used by TraceIdeal2.
lemma representativeNeSelf_mem_classOf3
  (s : Setup_spo α) (x : {x // x ∈ s.V}) (hx : 2 ≤ (classOf s ⟦x⟧).card) :
  s.setoid.r (representativeNeSelf2 s x hx) x :=
by
  dsimp [representativeNeSelf2]
  exact representativeNeSelf_mem_classOf2 s x hx



-----------------------
--Element correspondence.
-----------------------

--Supporting elements from s.V to s.V.erase x.
noncomputable def toErased (s : Setup_spo α)
  (x : {x : α // x ∈ s.V})
  (hx : (classOf s ⟦x⟧).card ≥ 2) :
  { y // y ∈ s.V } → { y // y ∈ s.V.erase x } :=
  fun z =>
    if h : z = x then
      let z' := representativeNeSelf s x hx
      ⟨z'.val, by
        simp [Finset.mem_erase]

      ⟩
    else
      ⟨z.val, by
        simp [Finset.mem_erase, h]
        exact Subtype.coe_ne_coe.mpr h⟩

--toErased map is an identity map if it is different from x.
private lemma toErased_eq_ne
  (s : Setup_spo α) (x z : {x // x ∈ s.V})
  (hx : 2 ≤ (classOf s ⟦x⟧).card)
  (h : z ≠ x) :
  toErased s x hx z = ⟨z.val, by
    simp [Finset.mem_erase]
    exact Subtype.coe_ne_coe.mpr h⟩ :=
by
  unfold toErased
  simp only
  split
  · contradiction
  · rfl

--On the other hand, when x and y are equal and x and z are equal, y and z are equal, so the destination of y and z are equal.
/-
lemma Quotient.eq
  (s : Setup_spo2 α) (y z : {x : α // x ∈ s.V})
  (eq: s.setoid.r y z):
  @Quotient.mk _ s.setoid y = @Quotient.mk _ s.setoid z :=
by
  simp_all only [Quotient.eq]
-/

-- If y and z are the same equivalent, then the destination is the same equivalent.
--It is also used by TraceIdeal.
--In the reverse direction, use toErased_eqx or toErased_eq_lem.
lemma toErased_eq
  (s : Setup_spo α) (x y z : {x : α // x ∈ s.V})
  (hx : 2 ≤ (classOf s ⟦x⟧).card)
  (q_eq:@Quotient.mk _ s.setoid y = @Quotient.mk _ s.setoid z):
   @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx y) = @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx z) :=
by
  dsimp [toErased]
  split
  · split
    ·
      rename_i h h_1
      subst h_1 h
      simp_all only [Subtype.coe_eta]
    · have a_eq_r: (toErased s x hx y) = (representativeNeSelf s x hx) := by
          dsimp [toErased]
          simp
          rename_i h h_1
          intro h_2
          subst h
          ext : 1
          simp_all only
          simp_all only [not_true_eq_false]
      have : @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx y) = @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx z) :=
      by
        dsimp [toErased]
        dsimp [restrictedSetoid]
        simp
        rename_i h_1
        simp only [h_1]
        split_ifs with h_2
        · rename_i h
          subst h
          simp_all only [Quotient.eq]
        .
          rename_i h

          have : s.setoid.r y z := by
            subst h
            simp_all only [Quotient.eq, not_false_eq_true]
          let rsx :=(⟨representativeNeSelf s x hx, by
              subst h
              simp_all only [Quotient.eq, not_false_eq_true]
              obtain ⟨val, property⟩ := y
              obtain ⟨val_1, property_1⟩ := z
              simp_all only [Subtype.mk.injEq]
              rw [← a_eq_r]
              simp_all only
              erw [← a_eq_r]
              simp_all only
              exact coe_mem _
            ⟩: { x // x ∈ s.V })
          have : s.setoid.r rsx y := by
            dsimp [rsx]
            let rmc2 := representativeNeSelf_mem_classOf2 s x hx
            subst h
            simp_all only [Quotient.eq, not_false_eq_true]
          have : s.setoid.r rsx z := by
            apply s.setoid.iseqv.trans
            · dsimp [rsx]
              let rmc2 := representativeNeSelf_mem_classOf2 s x hx
              subst h
              exact rmc2
            · dsimp [rsx]
              subst h
              simp_all only [Quotient.eq, not_false_eq_true, rsx]
          subst h
          simp_all only [Quotient.eq, rsx]

          exact this
      rw [a_eq_r] at this
      rw [this]
      simp

      dsimp [restrictedSetoid]
      dsimp [Setoid.comap]
      dsimp [toErased]
      rename_i h h_1
      subst h
      simp_all only [Quotient.eq, ↓reduceDIte]
      obtain ⟨val, property⟩ := y
      obtain ⟨val_1, property_1⟩ := z
      simp_all only
      rfl
  · split
    ·
      have a_eq_r: (toErased s x hx z) = (representativeNeSelf s x hx) := by
          dsimp [toErased]
          simp
          rename_i h h_1
          intro h_2
          subst h_1
          ext : 1
          simp_all only
          exact False.elim (h_2 rfl)
      have : @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx y) = @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx z) :=
      by
        dsimp [toErased]
        dsimp [restrictedSetoid]
        simp
        rename_i h_1

        simp only [h_1]
        split_ifs
        · rename_i h
          have : s.setoid.r y z := by
            subst h_1
            simp_all only [Quotient.eq]
          let rsx :=(⟨representativeNeSelf s x hx, by
              simp_all only [Quotient.eq, not_false_eq_true]
              obtain ⟨val, property⟩ := y
              obtain ⟨val_1, property_1⟩ := z
              rw [← a_eq_r]
              simp_all only
              erw [← a_eq_r]
              simp_all only
              exact coe_mem _
            ⟩: { x // x ∈ s.V })
          have : s.setoid.r rsx y := by
            dsimp [rsx]
            let rmc2 := representativeNeSelf_mem_classOf2 s x hx

            simp_all only [Quotient.eq, not_false_eq_true]
            exact
              Setoid.symm' s.setoid (Setoid.trans' s.setoid this (id (Setoid.symm' s.setoid rmc2)))
          have : s.setoid.r rsx z := by
            apply s.setoid.iseqv.trans
            · dsimp [rsx]
              let rmc2 := representativeNeSelf_mem_classOf2 s x hx
              exact rmc2
            · dsimp [rsx]
              simp_all only [Quotient.eq, not_false_eq_true, rsx]
              subst h_1
              rfl
          subst h_1
          simp_all only [rsx]

          dsimp [representativeNeSelf]
          tauto
      rw [a_eq_r] at this
      rw [←this]
      simp
      dsimp [restrictedSetoid]
      dsimp [Setoid.comap]
      dsimp [toErased]
      simp
      rename_i h_1
      subst h_1
      simp_all only [Quotient.eq, ↓reduceDIte]
      rfl
    ·
      simp_all only [Quotient.eq]
      exact q_eq

--The opposite direction of the above proposition.When it entered the equivalent class of x to which it was transferred, it was originally the same value as x.
--It is also used by TraceIdeal.
lemma toErased_eqx
  (s : Setup_spo α) (x : {xx : α // xx ∈ s.V}) (y z : {xx : α // xx ∈ s.V.erase x.val})
  -- (hx : 2 ≤ (classOf s ⟦x⟧).card)
  (equivyz: (restrictedSetoid s x).r y z) :
  s.setoid.r ⟨y.val, by
    have : s.V.erase x.val ⊆ s.V := by
      exact Finset.erase_subset _ _
    obtain ⟨val_1, property_1⟩ := y
    exact this property_1
  ⟩
  ⟨z.val, by
    have : s.V.erase x.val ⊆ s.V := by
      exact Finset.erase_subset _ _
    obtain ⟨val_1, property_1⟩ := z
    exact this property_1
  ⟩
  :=
  by
    exact equivyz

--

-------------
---Response to trace equivalents
--The world where old is big, new is small

--Since both old and new equivalence classes are all injected, in order to define fq, we need to create a map of their correspondence.
def toOld (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  : Quotient (restrictedSetoid s x) → Quotient s.setoid :=
  λ newCls =>
    Quotient.liftOn newCls
      (fun (y : {y : α // y ∈ s.V.erase x.val}) =>
        @Quotient.mk _ s.setoid (⟨y.val, by exact Finset.mem_of_mem_erase y.property⟩ : {z // z ∈ s.V})
      )
      (by
        intros a b hab
        apply Quotient.sound
        exact hab
      )

--Response from old equivalence classes to new equivalence classes.
noncomputable def toNew (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2)
  : Quotient s.setoid → Quotient (restrictedSetoid s x) :=
  fun oldCls =>
    @Quotient.liftOn {x // x ∈ s.V} (Quotient (restrictedSetoid s x)) s.setoid oldCls
    (fun z => @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx z))
    (by
      intros a b hab
      apply toErased_eq s x a b hx
      simp_all only [ge_iff_le, Quotient.eq]
      exact hab
    )

--New and Old will return to the original equivalent class.
--I'm not sure how to use Quotient.inductionOn, but I've proved it.
lemma NewOld_id (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2)
  (Cls : Quotient s.setoid) :
  toOld s x (toNew s x hx Cls) = Cls := by
  induction Cls using Quotient.inductionOn
  case h a =>
    dsimp [toNew]
    dsimp [toOld]
    dsimp [toErased]
    dsimp [representativeNeSelf]

    by_cases h:x ∈ (classOf s ⟦a⟧)
    case pos =>
      by_cases h_1 : a = x
      case pos =>
        subst h_1
        simp
        dsimp [classOf] at h
        rw [Finset.mem_filter] at h
        let cc := Classical.choose_spec (exists_ne_of_one_lt_card hx a)
        simp_all only [mem_attach, and_self]
        obtain ⟨left, right⟩ := cc
        simp_all only [ne_eq]
        dsimp [classOf] at left
        rw [Finset.mem_filter] at left
        obtain ⟨left_1, right_1⟩ := left
        exact Quotient.eq''.mp right_1
      case neg =>
        dsimp [classOf] at h
        rw [Finset.mem_filter] at h
        obtain ⟨val, property⟩ := a
        obtain ⟨val_1, property_1⟩ := x
        simp_all only [Subtype.mk.injEq]
        simp_all only [↓reduceDIte]

    case neg =>
      dsimp [classOf] at h
      simp only [Finset.mem_filter] at h
      simp at h
      simp
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := a
      simp_all only [Subtype.mk.injEq]
      split
      next h_1 =>
        subst h_1
        simp_all only [Subtype.coe_eta]
        contrapose! h
        simp_all only [ne_eq]
        rfl
      next h_1 =>
        simp_all only
        rfl

lemma OldNew_id (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2)
  (Cls : Quotient (restrictedSetoid s x)) :
  toNew s x hx (toOld s x Cls) = Cls :=
by
  induction Cls using Quotient.inductionOn
  case h a =>
    dsimp [toNew]
    dsimp [toOld]
    dsimp [toErased]
    dsimp [representativeNeSelf]
    have: a.val ≠ x.val := by
      dsimp [representativeNeSelf]
      obtain ⟨val_1, property_1⟩ := a
      simp_all only [Subtype.mk.injEq]
      simp_all only [ge_iff_le, mem_erase, ne_eq, not_false_eq_true]
    simp_all only [ne_eq, Subtype.coe_eta, dite_eq_ite, Quotient.eq]
    obtain ⟨val, property⟩ := x
    simp_all only [Subtype.mk.injEq, ↓reduceIte]
    simp_all only [ge_iff_le]
    rfl


--Does it need to indicate that the order is saved in toNew or toOld?To do this, it is necessary that the order be introduced in a new equivalence structure.
--Is it better to introduce it in stages?To do this, first prove that it will become setup_spo.
-- It's up to fq and loop is not defined yet.Maybe it's better to create something like setup_spo0.


noncomputable def setup_trace_base (s : Setup_spo α)(x: s.V) (hx:(classOf s (@Quotient.mk _ s.setoid x
)).card ≥ 2): Setup_spo_base α :=
{
  V := s.V.erase x,
  nonemp := by
    have : (classOf s (@Quotient.mk _ s.setoid x)).card > 1 := by
      exact hx
    have : ∃ x0, x0 ∈ classOf s (@Quotient.mk _ s.setoid x) ∧ x0 ≠ x := by
      exact exists_ne_of_one_lt_card hx x
    simp_all only [ge_iff_le, gt_iff_lt, ne_eq, Subtype.exists, coe_mem, erase_nonempty, nontrivial_coe]
    obtain ⟨val, property⟩ := x
    obtain ⟨w, h⟩ := this
    obtain ⟨w_1, h⟩ := h
    obtain ⟨left, right⟩ := h
    simp_all only [Subtype.mk.injEq]
    constructor
    · simp_all only [mem_coe, ne_eq]
      apply And.intro
      · apply w_1
      · use val

  setoid := restrictedSetoid s x

  fq := fun q => toNew s x hx (s.fq (toOld s x q))
}

private lemma setup2_trace_fq_n (s : Setup_spo α) (x: s.V) (hx:(classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2) (n :Nat):
  ((setup_trace_base s x hx).fq)^[n] = fun q => toNew s x hx (s.fq^[n] (toOld s x q)) := by
  dsimp [setup_trace_base]
  induction n
  case zero =>
    simp_all only [Function.iterate_zero, id_eq]
    let no := OldNew_id s x hx
    simp_all only [no]
    obtain ⟨val, property⟩ := x
    simp_all only
    rfl

  case succ n ih =>
    simp_all only [Function.iterate_succ, ih]
    simp
    rw [←ih]
    funext q
    dsimp [setup_trace_base]
    let no := NewOld_id s x hx
    simp_all only [no]

--Use it with setup_trace_noLoop.
-- Also used for functionalSPO2.
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

--Use with setup_trace or setup_trace_spo2.
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

--trace, this is the premise of Setup_spo, not Setup_spo2.
noncomputable def setup_trace (s : Setup_spo α)(x: s.V) (hx:(classOf s (@Quotient.mk _ s.setoid x
)).card ≥ 2): Setup_spo α :=
{
  V := s.V.erase x,
  nonemp := (setup_trace_base s x hx).nonemp,
    setoid := restrictedSetoid s x
  fq := fun q => toNew s x hx (s.fq (toOld s x q))

  noLoop := by
    intro q1 q2
    intro h1 h2

    exact setup_trace_noLoop s x hx q1 q2 h1 h2

  spo := partialOrderOfFq (setup_trace_base s x hx).fq (by
      intro q1 q2
      intro h1 h2
      exact setup_trace_noLoop s x hx q1 q2 h1 h2
  )
  h_spo := by
    obtain ⟨val, property⟩ := x
    simp_all only
    rfl
}


private lemma toErased_eq_lem (s : Setup_spo α) (x : {x : α // x ∈ s.V})
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

--Equivalent types that differ from x are identity maps.Used in excess discussions such as toNew_classOf.
private lemma toNew_card_eq (s : Setup_spo α) (x : {x : α // x ∈ s.V})
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

-- Equivalent classes that do not include x do not change in size even if traced.
-- Used with trace_excess_decrease.
lemma toNew_classOf (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2)
  (cls : Quotient s.setoid) :
   cls ≠ (@Quotient.mk _ s.setoid x) →
    (classOf s cls).card  = (classOf (setup_trace s x hx) (toNew s x hx cls)).card :=
by
  intro h
  dsimp [setup_trace]
  dsimp [toNew]
  dsimp [classOf]
  let tce := toNew_card_eq s x cls hx h

  let src := filter (fun a : {y // y ∈ s.V} => Quotient.mk'' a = cls) s.V.attach
  let tgt := filter (fun a : {y // y ∈ s.V.erase x} =>
      Quotient.mk'' a = cls.liftOn (fun z => ⟦toErased s
       x hx z⟧)
        (by
          intro a b hab
          show Quotient.mk'' (toErased s x hx a) = Quotient.mk'' (toErased s x hx b)
          have : s.setoid.r a b :=
          by
            exact hab
          let tee := toErased_eq s x a b hx
          apply tee
          simp_all only [ne_eq, Quotient.eq]
        )
    ) (s.V.erase x).attach

  have tgt_classOf : tgt = classOf (setup_trace s x hx) (toNew s x hx cls) := by
    dsimp [tgt]
    dsimp [classOf]
    dsimp [setup_trace]
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


  have : src.image Subtype.val = tgt.image Subtype.val := by
    dsimp [src]
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

      have yinsVe:y ∈ (setup_trace s x hx).V := by
        dsimp [setup_trace]
        simp_all only [mem_erase, ne_eq, not_false_eq_true, and_self]
      let cq := (classOf_quotient  (setup_trace s x hx) ⟨y,yinsVe⟩ (toNew s x hx cls)).mp
      apply cq

      have : toNew s x hx (@Quotient.mk _ s.setoid ⟨y,w⟩) = @Quotient.mk _ (restrictedSetoid s x) ⟨y, yinsVe⟩ := by
        dsimp [toNew]
        dsimp [restrictedSetoid]

        simp_all only [mem_erase, ne_eq, not_false_eq_true, and_self]
        dsimp [toErased]
        split
        · let rnsm := representativeNeSelf_mem_classOf s x hx
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
      have yinsVe:y ∈ (setup_trace s x hx).V := by
        dsimp [setup_trace]
        simp_all only [mem_erase, ne_eq, not_false_eq_true, and_self]
      let cq := (classOf_quotient (setup_trace s x hx) ⟨y, yinsVe⟩ (toNew s x hx cls)).mpr
      have tnqlem: toNew s x hx (@Quotient.mk _ s.setoid ⟨y,w.2⟩) = @Quotient.mk _ (restrictedSetoid s x) ⟨y, yinsVe⟩ := by
        dsimp [toNew]
        dsimp [restrictedSetoid]
        simp_all only [mem_erase, ne_eq, not_false_eq_true, and_self]
        dsimp [toErased]
        split
        · let rnsm := representativeNeSelf_mem_classOf s x hx
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
      have yinco:⟨y, yinsVe⟩ ∈ classOf (setup_trace s x hx) (toNew s x hx cls) :=
      by
        simp_all only [mem_filter, mem_attach, true_and, Finset.mem_image, Subtype.exists, mem_erase, ne_eq,
          exists_and_right, exists_eq_right, not_true_eq_false, coe_mem, and_true, IsEmpty.exists_iff,
          not_false_eq_true, tgt, src]
      specialize cq yinco
      have :toNew s x hx (@Quotient.mk _ s.setoid ⟨y,w.2⟩) = toNew s x hx cls :=
      by
        simp_all only [mem_filter, mem_attach, true_and, Finset.mem_image, Subtype.exists, mem_erase, ne_eq,
          exists_and_right, exists_eq_right, not_true_eq_false, coe_mem, and_true, IsEmpty.exists_iff,
          not_false_eq_true, tgt, src]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := w
        simp_all only [src]
        rfl
      let ca := congrArg (toOld s x ) this
      rw [NewOld_id s x hx] at ca
      rw [NewOld_id s x hx] at ca
      exact ca

  have : src.card = tgt.card := by

    have h_inj_src : Set.InjOn Subtype.val src.toSet := by
      intros a _ b _ hab
      exact Subtype.ext hab

    have h_inj_tgt : Set.InjOn Subtype.val tgt.toSet := by
      intros a _ b _ hab
      exact Subtype.ext hab

    have h_card_src : (Finset.image Subtype.val src).card = src.card :=
      (Finset.card_image_iff.mpr h_inj_src)

    have h_card_tgt : (Finset.image Subtype.val tgt).card = tgt.card :=
      (Finset.card_image_iff.mpr h_inj_tgt)

    have : src.card = tgt.card := by
      rw [←h_card_src, this, h_card_tgt]

    exact this

  simp_all only [mem_filter, mem_attach, true_and, Finset.mem_image, Subtype.exists, mem_erase, ne_eq, exists_and_right,
    exists_eq_right, not_true_eq_false, coe_mem, and_true, IsEmpty.exists_iff, not_false_eq_true, tgt, src]
