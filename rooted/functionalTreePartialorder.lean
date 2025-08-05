-- Setup2 is defined in this file.
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
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
import rooted.functionalTreePreorder


open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

-- Setup2 defined here refers to the partial order on the equivalence class setoid.You can use s.po and s.fq.
--If there is a relationship between magnitude and size in the partial order, the previous order in which you pull back it also has a relationship between magnitude and size.
--If there is a relationship between magnitude and size in the previous order, even if the partial order is pushforwarded, there is a relationship between magnitude and size.
-- Equivalent types with a magnitude of 2 or more of the preorder become the maximum element of the partial order.(Not shown here?)
-- The maximum element of preorder is the maximum element of the equivalent class.(Not shown here?)


-------------------
---Preparing for Setup2 definitions
--------------------

-- Is the reason the proof is longer than quoteient_partial_order because preorder is defined indirectly?
-- It is also used in Preorder_eq_PartialOrder.
-- It is used through the lemma of this file without directly using this definition.
def partialOrder_from_preorder (s : Setup α) : PartialOrder (Quotient s.setoid) where
  le := by
    exact Quotient.lift₂ (fun x y => s.pre.le x y)
      (by

        intros a₁ b₁ a₂ b₂ h₁ h₂

        have h₁' := s.h_setoid ▸ h₁
        have h₂' := s.h_setoid ▸ h₂

        simp [setoid_preorder] at h₁' h₂'

        rcases h₁' with ⟨h₁_le, h₁_ge⟩
        rcases h₂' with ⟨h₂_le, h₂_ge⟩

        apply propext
        constructor
        · intro h
          exact le_implies_le_of_le_of_le h₁_ge h₂_le h
        · intro h
          exact le_implies_le_of_le_of_le h₁_le h₂_ge h

      )
  le_refl := by
    intro xx
    simp [Quotient.lift₂]
    induction xx using Quotient.inductionOn
    simp_all only [Quotient.lift_mk, le_refl]

  le_trans := by
    intro x y z
    induction x using Quotient.inductionOn
    simp_all only [Quotient.lift_mk, Quotient.lift₂]
    induction y using Quotient.inductionOn
    induction z using Quotient.inductionOn
    simp_all only [Quotient.lift_mk, Quotient.lift₂]
    rename_i a a_1 a_2
    intro a_3 a_4
    exact a_3.trans a_4

  le_antisymm := by
    intro x y

    induction x using Quotient.inductionOn
    rename_i a
    intro a_1 a_2
    simp_all only [Quotient.lift_mk]
    symm
    induction' y using Quotient.inductionOn with y
    simp_all only [Quotient.lift_mk, Quotient.eq]
    induction s
    rename_i h_pre setoid h_setoid
    subst h_pre h_setoid
    simp_all only [AntisymmRel.setoid_r]
    trivial

-- Setup with partial order on equivalence classes.Is the strength the assumption the same as Setup?You can then define Setup2 from Setup.Setup_to_Setup2
-- By setting it to Setup2, you can use s.po.
-- Refactoring schedule: It would have been better to have set po to def without having to set it to Setup and Setup2.
-- The above instance is different from s.po.le, so def is better than instance.
structure Setup2 (α : Type) [Fintype α] [DecidableEq α] extends Setup α where
  (po       : PartialOrder (Quotient setoid))
  (h_po     :  po = partialOrder_from_preorder toSetup)

-- It overlaps with the previously defined quotaent_partial_order.
instance (s : Setup2 α) : PartialOrder (Quotient s.setoid) := s.po

-- Setup and Setup2 have the same assumption strength.
def Setup_to_Setup2 (s : Setup α) : Setup2 α :=
  {
    V := s.V
    f := s.f
    setoid := s.setoid
    pre := s.pre
    nonemp := s.nonemp
    valid := s.valid
    h_pre := s.h_pre
    h_setoid := s.h_setoid
    po := partialOrder_from_preorder s
    h_po := rfl
  }



------------------------
-- A lemma showing the relationship between s.pre and s.po.
---------------------------

-- The partial order on the equivalence class is compatible with the magnitude relationship of the previous order.
-- I'm using it below and from outside.
-- It automatically uses an instance of s.po even without inst included.
lemma pullback_preorder_lemma (s : Setup2 α)
 (j1 j2 : (Quotient s.setoid)) (x1 x2 : s.V) :
  Quotient.mk s.setoid x1 = j1 → Quotient.mk s.setoid x2 = j2 → s.po.le j1 j2 → s.pre.le x1 x2 :=
by
  intro h1 h2 h3
  rw [@Setup2.h_po] at h3
  dsimp [partialOrder_from_preorder] at h3
  simp [LE.le, partialOrder_from_preorder, Quotient.lift₂] at h3
  subst h2 h1
  simp_all only [Quotient.lift_mk]
-- The relationship between the magnitude and size of elements and the magnitude of equivalence classes.If there is a relationship in the previous order, there is a relationship in the semi order.
--I'm using it below, and I'm using it from there as well.
-- Is the lemma above in the reverse direction?
--Used with Preorder_eq_PartialOrder etc.
lemma pushforward_preorder_lemma (s : Setup2 α) (x1 x2 : s.V) :
  s.pre.le x1 x2 → s.po.le (Quotient.mk s.setoid x1)  (Quotient.mk s.setoid x2) :=
by
  intro h
  rw [@Setup2.h_po]
  dsimp [partialOrder_from_preorder]
  simp_all only

--------------------------
-- Definitions and lemma regarding the maximum elements.

-- A predicate that represents the "maximum" in `(Quotient setoid_preorder, ≤)` on the quotient set.
--This order is the order of Partial order.Maybe I haven't used it yet.Rewrite with setup.
def isMaximalQ (s : Setup2 α) (x : Quotient (s.setoid)) : Prop :=
  ∀ y, s.po.le x y → s.po.le y x

-- The relationship between the maximum value as an element and the maximum value class.It's used in a different file.
lemma isMaximal_iff (s: Setup2 α) (a : s.V) :
  isMaximal s.toSetup a ↔ isMaximalQ s (Quotient.mk s.setoid a) := by
  constructor
  · --------------------
    intro ha
    intro x hx
    rcases Quotient.exists_rep x with ⟨b, rfl⟩
    dsimp [isMaximal] at ha
    specialize ha b
    have : a ≤ b := by
      exact pullback_preorder_lemma s (Quotient.mk s.setoid a) (Quotient.mk s.setoid b) a b rfl rfl hx
    have : b ≤ a := by
      exact ha this
    apply pushforward_preorder_lemma s
    simp_all only [imp_self]
  ·
    intro ha
    intro b hab
    dsimp [isMaximalQ] at ha
    have : s.po.le (Quotient.mk s.setoid a) (Quotient.mk s.setoid b) := by
      exact pushforward_preorder_lemma s a b hab
    have : s.po.le (Quotient.mk s.setoid b) (Quotient.mk s.setoid a) := by
      simp_all only [imp_self]
    apply pullback_preorder_lemma s ⟦b⟧ ⟦a⟧ b a rfl rfl
    simp_all only

-------------------
----Lemma related to fq.
--------------------

-- refers to a Quotient one above the partial order of the setoid.
-- It might be possible to set it instead of Setup2.
def fq (s: Setup2 α) (q:(Quotient s.setoid)):
  (Quotient s.setoid) :=
 Quotient.lift (fun (x:s.V) => Quotient.mk s.setoid (s.f x))
    (by
      intros a b h
      -- First, expand the setoid definition
      dsimp [Quotient.lift]
      rw [@Quotient.eq]
      apply (Setoid.comap_rel s.f s.setoid a b).mp
      have :s.setoid a b := by
        exact h
      rw [← @Quotient.eq_iff_equiv] at h
      let foe := f_on_equiv s.toSetup a b this
      simp_all only [Quotient.eq]
      exact foe
    ) q

-- It's the same whether you take Quotient and then apply fq, or take f and then take Quotient.
--The argument to fq must be set to Setup2 instead of Setup.I think I can use reach.
private lemma f_on_equiv_n
  (s: Setup2 α) (x : s.V) :
  ∀ n:Nat, Quotient.mk s.setoid (s.f^[n] x) = (fq s)^[n] (Quotient.mk s.setoid x) :=
by
  intro n
  induction n generalizing x
  case zero =>
    simp_all only [Finset.mem_univ, Quotient.lift_mk, Quotient.mk]
    simp_all only [Function.iterate_zero, id_eq]
  case succ n ih =>
    simp_all only [Function.iterate_succ, Quotient.mk]
    rw [@Function.comp_def]
    rw [@Function.comp_def]
    rw [ih (s.f x)]
    simp_all only [Subtype.forall]
    congr 1

-- It is also possible to use lemma to take elements from any equivalence class.It would be good to set up, but I'll only use it here.Quot.out would also be fine.
private lemma quotient_representative (s: Setup2 α) (q: Quotient s.setoid) :
  ∃ x : s.V, q = Quotient.mk s.setoid x :=
by
  simp_all only [Subtype.exists]
  rcases q with ⟨x,hx⟩
  exact ⟨x, hx, rfl⟩

private lemma pre_po_lemma (s: Setup2 α) (x y :s.V) :
 s.pre.le x y ↔ s.po.le (Quotient.mk s.setoid x) (Quotient.mk s.setoid y) := by
  constructor
  · intro h
    exact pushforward_preorder_lemma s x y h
  · intro h
    exact pullback_preorder_lemma s ⟦x⟧ ⟦y⟧ x y rfl rfl h


--Can you rewrite using reach?The opposite is fq_lemma_rev.

lemma fq_lemma (s: Setup2 α) (qx:Quotient s.setoid) :
  ∀ qy :(Quotient s.setoid), s.po.le qx qy → ∃ n:Nat, qy = ((fq s)^[n]) qx :=
by
  intro qy hqy
  obtain ⟨x, hx⟩ := quotient_representative s qx
  obtain ⟨y, hy⟩ := quotient_representative s qy
  have : s.pre.le x y := by
    rw [hx] at hqy
    rw [hy] at hqy
    apply pullback_preorder_lemma s qx qy x y
    subst hx hy
    simp_all only
    subst hx hy
    simp_all only
    subst hx hy
    simp_all only
  let il := iteratef_lemma_ref s.toSetup x y this
  obtain ⟨n, h⟩ := il
  use n

  let fone := f_on_equiv_n s x
  rw [←hx] at fone
  rw [←fone n]
  rw [hy]
  rw [←h]

--The direction of the size and size of the PO to FQ.Used as the base case of fq_lemma_rev.
-- For one level.
-- I'm using it below.
private lemma fq_lemma_rev_one (s: Setup2 α) (qx :Quotient s.setoid) :
  s.po.le qx ((fq s) qx) :=
by

  obtain ⟨x,hx⟩ := quotient_representative s qx

  let y := s.f x
  have hy: ((fq s) qx) = Quotient.mk s.setoid y := by
    rw [@Setup.h_setoid] at qx
    rw [setoid_preorder] at qx
    simp_all only [Quotient.lift_mk]
    subst hx
    simp_all only [y]
    rfl
  let ppl := pre_po_lemma s x y
  have : s.pre.le x y := by
    dsimp [y]
    exact f_and_pre s.toSetup x (s.f x) rfl
  subst hx
  simp_all [y]

--What you can do with FQ's Iteration has something to do with size.The reverse of fq_lemma.
-- Reach_leq can be rewritten using reach in functionalSPO, so it's a good idea to use that.
-- I used it from outside.
lemma fq_lemma_rev (s: Setup2 α) (qx qy:Quotient s.setoid) :
  (∃ n:Nat, qy = ((fq s)^[n]) qx) → s.po.le qx qy :=
by
  intro h

  obtain ⟨n, h⟩ := h
  rw [h]

  induction n generalizing qx
  case zero =>
    subst h
    simp_all only [Function.iterate_zero, id_eq, le_refl]
  case succ n ih =>
    subst h
    simp_all only [Function.iterate_succ, Quotient.mk]
    rw [@Function.comp_def]

    simp_all only [Subtype.forall]

    have : s.po.le qx ((fq s) qx) := by
      apply fq_lemma_rev_one

    let ihh := ih (fq s qx)
    simp_all only [ge_iff_le]
    apply le_trans
    · exact this
    · simp_all only [Function.comp_apply]

--This one is the PO, not the SPO.I use it outside too.I changed my name.
lemma reach_po_leq (s : Setup2 α) (x y : Quotient s.setoid) :
  reach (fq s) x y → s.po.le x y := by
  intro h
  rw [s.h_po]
  dsimp [reach] at h
  let fql := fq_lemma_rev s x y
  obtain ⟨n, hn⟩ := h
  rw [←hn]
  have :(∃ n, y = (fq s)^[n] x) := by
    use n
    subst hn
    simp_all only
  specialize fql this
  rw [←hn] at fql
  convert fql
  rw [s.h_po]
