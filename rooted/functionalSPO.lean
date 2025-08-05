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
--import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne
import rooted.functionalCommon
import rooted.functionalTreePreorder
import rooted.functionalTreePartialorder

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

--This file is from the part of Setup_spo that was before it entered trace.

--If you define up to fq, the previous order on the equivalence class can be determined.As a hypothetical, it is weak because the loop of f is allowed.Prove that there is no loop and it's partially ordered.
structure Setup_spo_base (α : Type) [Fintype α] [DecidableEq α] where
  (V : Finset α)
  (nonemp   : V.Nonempty)
  (setoid : Setoid {x : α // x ∈ V})
  (fq : Quotient setoid → Quotient setoid)

--Since it's related to partial order, I moved from common.What to use in the Setup_spo definition.
--But it is referenced from three external files.
def partialOrderOfFq {A : Type} (f : A → A)
  (noLoop : ∀ x y, reach f x y → reach f y x → x = y)
  : PartialOrder A :=
{ le := reach f
  le_refl := by
    intro x
    dsimp [reach]
    use 0
    simp_all only [Function.iterate_zero, id_eq]

  le_trans := by
      intro x y z ⟨n, hn⟩ ⟨m, hm⟩
      exists (n + m)
      subst hn hm
      let fi := (Function.iterate_add_apply f m n x)
      rw [add_comm] at fi
      exact fi

  , le_antisymm := by
      intro x y hxy hyx
      exact noLoop x y hxy hyx
}

--The fq here is the fq from Setup_spo_base.
structure Setup_spo (α : Type) [Fintype α] [DecidableEq α] extends Setup_spo_base α where

  (noLoop : ∀ x y : Quotient setoid,
    (reach fq x y → reach fq y x → x = y))
  (spo : PartialOrder (Quotient setoid))
  (h_spo : spo = partialOrderOfFq fq noLoop)

def isMaximal_spo (s: Setup_spo α) (x : Quotient s.setoid) : Prop :=
  ∀ y : Quotient s.setoid,
  s.spo.le x y → s.spo.le y x

-- Matters related to equivalence classes in the Setup_spo framework.

--Rears to that for Quotient.A set of vertices.
-- It may not have been necessary as it is the same as the definition of eqClass.That's for Setup2.I was able to unify it by using setoid as an argument.
def classOf (s : Setup_spo α) (q : Quotient s.setoid) [DecidableEq (Quotient s.setoid)]  : Finset {x // x ∈ s.V} :=
  Finset.filter (fun (a : {x // x ∈ s.V}) => @Quotient.mk'' _ s.setoid a = q) s.V.attach

--I tried defining it for setoid.This might not be better.
noncomputable def classOfsetoid (V: Finset α) (std: Setoid {x : α // x ∈ V}) (x : {x : α // x ∈ V}) :
  Finset {x : α // x ∈ V} :=
  Finset.filter (fun (a : {x : α // x ∈ V}) => std.r x a) V.attach

--The entire vertex equivalent to one element is classOf.Points with arguments s.V.
noncomputable def classOfx (s : Setup_spo α) (x : {x : α // x ∈ s.V}) :
  Finset {x : α // x ∈ s.V} :=
  classOf s (@Quotient.mk _ s.setoid x)
--Equivalence class must be non-empty.
lemma classOf_nonempty (s : Setup_spo α) (q : Quotient s.setoid) :
  (classOf s q).Nonempty := by
  dsimp [classOf]
  rw [Finset.filter_nonempty_iff]
  let a := Quotient.out q
  use a
  constructor
  · exact mem_attach s.V a
  · exact Quotient.out_eq q

--It doesn't need to be bothered to define it.For a vertex set, the corresponding set of Quotients.
--I've used it in several places.
noncomputable def QuotientOf (s: Setup_spo α) (xx : Finset {x : α // x ∈ s.V}) :
  Finset (Quotient s.setoid) :=
  xx.image (@Quotient.mk _ s.setoid)

--The relationship between the equivalent value of setoid and classOf.It is also used by TraceIdeal.
--Since it has no direct connection to trace, I moved to SPO etc.Does it overlap with the theorem above?
lemma classOf_setoid
  (s : Setup_spo α) (y z: {x : α // x ∈ s.V}) :
  s.setoid.r y z ↔ y ∈ (classOf s ⟦z⟧)  :=
by
  apply Iff.intro
  · intro h
    dsimp [classOf]
    rw [Finset.mem_filter]
    constructor
    · simp_all only [mem_attach]
    · dsimp [classOf]
      simp_all only [Quotient.eq]
  · intro h
    dsimp [classOf] at h
    rw [Finset.mem_filter] at h
    simp_all only [mem_attach, Quotient.eq, true_and]

--The relationship between the same thing in classOf and the same thing in setoid.
--It may be obvious from the above lemma and definition.I'm using it below.
lemma classOf_quotient
  (s : Setup_spo α) (y : {x : α // x ∈ s.V}) (q:Quotient s.setoid) :
  q = @Quotient.mk' _ s.setoid y ↔ y ∈ (classOf s q) := by
  dsimp [classOf]
  rw [Finset.mem_filter]
  constructor
  ·
    intro a
    subst a
    simp_all only [mem_attach, true_and]
    obtain ⟨val, property⟩ := y
    rfl
  · dsimp [classOf]
    intro h
    symm
    exact h.2

--I myself fall into the same category.Use from outside.
lemma classOf_self
  (s : Setup_spo α) (x : {x : α // x ∈ s.V}) :
  x ∈ (classOf s ⟦x⟧) := by
  dsimp [classOf]
  rw [Finset.mem_filter]
  constructor
  · exact mem_attach s.V x
  · dsimp [classOf]

-- Matters related to reach regarding the framework of setup_spo.

lemma reach_leq (s : Setup_spo α) (q1 q2 : Quotient s.setoid) :
  reach s.fq q1 q2 → s.spo.le q1 q2 := by
  intro h
  rw [s.h_spo]
  dsimp [partialOrderOfFq] at *
  exact h

lemma reach_leq_rev (s : Setup_spo α) (q1 q2 : Quotient s.setoid) :
  s.spo.le q1 q2 →  reach s.fq q1 q2  := by
  intro h
  rw [s.h_spo] at h
  dsimp [partialOrderOfFq] at h
  dsimp [reach]
  exact h



--The corresponding Setup_spo element for Setup2.It will later be expanded to Setup_spo2.That's setup2_induces_spo.
def setup_setupspo (s: Setup2 α) : Setup_spo α :=
{
  V := s.V,
  nonemp := s.nonemp,
  setoid := s.setoid,
  fq := fq s
  noLoop := by
    have : ∀ q1 q2 : Quotient s.setoid, (reach (fq s) q1 q2 → reach (fq s) q2 q1 → q1 = q2) := by
      intro q1 q2 hxy hyx
      dsimp [reach] at *
      obtain ⟨x, hx⟩ := Quotient.exists_rep q1
      obtain ⟨y, hy⟩ := Quotient.exists_rep q2

      have : q1 ≤ q2 := reach_po_leq s q1 q2 hxy
      have : q2 ≤ q1 := reach_po_leq s q2 q1 hyx
      apply s.po.le_antisymm
      · subst hy hx
        simp_all only
      · exact this

    exact this,
  spo := partialOrderOfFq (fq s) (by
    have : ∀ x y : Quotient s.setoid, (reach (fq s) x y → reach (fq s) y x → x = y) := by
      intro x y hxy hyx
      dsimp [reach] at *
      have : s.po.le x y  = reach (fq s) x y := by
        let rl := reach_po_leq s x y hxy
        simp_all only [eq_iff_iff, true_iff, rl]
        obtain ⟨w, h⟩ := hxy
        obtain ⟨w_1, h_1⟩ := hyx
        subst h
        rw [← h_1]
        simp_all only
        rw [reach]
        simp_all only [exists_apply_eq_apply]
      have poxy: s.po.le x y := by
        dsimp [reach] at this
        rw [this]
        exact hxy
      have : s.po.le y x = reach (fq s) y x := by
        let rl := reach_po_leq s y x hyx
        simp_all only [eq_iff_iff, true_iff, rl]
        obtain ⟨w, h⟩ := hxy
        obtain ⟨w_1, h_1⟩ := hyx
        subst h
        rw [← h_1]
        simp_all only
        rw [reach]
        exact Exists.intro w_1 h_1
      have poyx: s.po.le y x := by
        dsimp [reach] at this
        rw [this]
        exact hyx
      apply s.po.le_antisymm
      exact poxy
      exact poyx
    intro x y a a_1
    exact this _ _ a a_1)
  h_spo := rfl
}

--eqClass and classOf are the same.classOf is different in that it is defined by setup_spo.
--Can be integrated.Is Setup enough, not Setup2?
--The locations used include TreeIdeal and SPO2.
lemma eqClass_Class_of (s: Setup2 α) (x : {x : α // x ∈ s.V}) :
  (eqClass_setup s.toSetup) x = classOf (setup_setupspo s) (@Quotient.mk' _ s.setoid x) := by
  dsimp [classOf]
  dsimp [eqClass_setup]
  dsimp [setup_setupspo]
  congr
  apply funext
  intro x
  rename_i x_1
  simp_all only [eq_iff_iff]
  obtain ⟨val, property⟩ := x_1
  obtain ⟨val_1, property_1⟩ := x
  apply Iff.intro
  · intro a
    symm
    exact Quotient.sound' a
  · intro a
    rw [Quotient.mk''_eq_mk] at a
    symm
    simp only [Quotient.mk'] at a
    simp_all only [Quotient.eq]



--Almost the same as above, but given q.
lemma eqClass_Class_of2 (s: Setup2 α) (q : Quotient s.setoid) :
  eqClass_setup s.toSetup (Quotient.out q) = (classOf (setup_setupspo s) q) :=
by
  rw [eqClass_Class_of]
  congr
  simp [Quotient.mk']

--Setup2 order can be extended to SPO order.This can also be integrated into the theorem above.
--Since it follows the parent in partial order, Setup2 instead of Setup.
--It appears in TreeIdeal.
-- It appears in Setup_spo2.On the Setup2 assumption, the lemma isMaximal_spo_iff is not used.
--Supported in setup2_induces_spo.
lemma spole_iff_po (s: Setup2 α) (x y : Quotient s.setoid) :
  s.po.le x y ↔ (setup_setupspo s).spo.le x y := by
  dsimp [setup_setupspo]
  dsimp [partialOrderOfFq]
  dsimp [reach]
  apply Iff.intro
  · intro h
    let fql := fq_lemma s x y h
    obtain ⟨n, hn⟩ := fql
    use n
    exact hn.symm
  · intro h
    obtain ⟨n, hn⟩ := h
    have :(∃ n, y = (fq s)^[n] x) := by
      use n
      subst hn
      simp_all only
    let fql := fq_lemma_rev s x y this
    exact fql
