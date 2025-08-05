--This file provides the basic definition of functional discussion.Setup etc.
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Tactic
--import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne

set_option maxHeartbeats 2000000

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

--This is here because it is necessary to state the Main theorem.It is not so commonly used by other parts.
--I wish I could add more common parts.If you change your assumptions all the time, like Setup, it is difficult to make the parts common.
--Setup only appears in Preorder, so I thought it would be possible to move the Setup section to Preorder.
--The same goes for preclosuresystem.
--In addition, some lemma related to the Setup definition.
--Part of the definition of --eqClass_setup.
--Reach.This may not depend on Setup.

--------------------------------------------------------------------------------------------------------------------------------
--The part required to define setup.
-- A function to create a RootedSet from --f.
--Is this the best form?Gives RootedSets on alpha.This form is used to define groupings.
--This definition is also referenced in the --functionalMain Primary theorem.
--The rootedset_from_setup is now available from Setup.
noncomputable def rootedset_onestem_eachvertex_V {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:Finset.Nonempty V): RootedSets α :=
{
  ground := V,
  rootedsets :=
  V.attach.image (λ v => ValidPair.mk ({(f v).val}:Finset α) v (by
    have : v ∉ ({f v}:Finset V) := by
      simp_all only [ne_eq, Subtype.forall, Finset.mem_singleton]
      obtain ⟨val, property⟩ := v
      apply Aesop.BuiltinRules.not_intro
      intro a
      exact valid _ _ a.symm
    simp
    by_contra h_contra
    simp_all only [Finset.mem_singleton, ne_eq]
    have h_eq : v = f v := by
      apply Subtype.eq
      exact h_contra
    contradiction
  ))

  inc_ground := by
    intros p hp
    specialize hp
    constructor
    · simp at hp
      obtain ⟨v, ⟨hv, ⟨hv_in, hp_in⟩⟩⟩ := hp
      simp
    ·
      simp_all only [Finset.mem_image, mem_attach, true_and, Subtype.exists]
      obtain ⟨w, h⟩ := hp
      obtain ⟨w_1, h⟩ := h
      subst h
      simp_all only

  nonempty_ground := by
    simp_all only [ne_eq, Subtype.forall, attach_nonempty_iff]
  }

--It is used when defining setup.Define preorder from f.
noncomputable def size_one_preorder {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty):
  Preorder { x // x ∈ V } := size_one_circuits_preorder (rootedset_onestem_eachvertex_V V f valid nonemp)


--This is the general story in which the previous order creates equivalence classes and then creates a partial order above it.Setoid has been introduced.Used for Setup.
def equiv_rel {α : Type} [Preorder α] (x y : α) : Prop := x ≤ y ∧ y ≤ x

lemma equiv_rel_refl {α : Type} [Preorder α]  : Reflexive (@equiv_rel α _) := fun x => ⟨le_refl x, le_refl x⟩

lemma equiv_rel_symm  {α : Type} [Preorder α] : Symmetric (@equiv_rel α _) :=
  fun (x y : α) (h : equiv_rel x y) => ⟨h.2, h.1⟩

lemma equiv_rel_trans {α : Type} [Preorder α] : Transitive (@equiv_rel α _) :=
  fun _ _ _ ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨le_trans h1 h3, le_trans h4 h2⟩

lemma equiv_rel_equiv {α : Type}  [Preorder α]: Equivalence (@equiv_rel α _) :=
  ⟨equiv_rel_refl, @equiv_rel_symm α _, @equiv_rel_trans α _⟩

--The definition of the setoid defined from preorder.Used in setup definition。
def setoid_preorder {α : Type}[Preorder α]: Setoid α := ⟨@equiv_rel α _, equiv_rel_equiv⟩

--It is strong enough to make normalized degree sum non-positive.
structure Setup (α : Type) [Fintype α] [DecidableEq α] where
  (V        : Finset α)
  (nonemp   : V.Nonempty)
  (f        : V → V)
  (valid    : ∀ v : V, f v ≠ v)
  (pre      : Preorder {x // x ∈ V})
  (h_pre    : pre = size_one_preorder V f valid nonemp)
  (setoid   : Setoid {x // x ∈ V})
  (h_setoid : setoid = setoid_preorder) --This is not an order, but up to the equivalent class.

--size_one_preorder is defined from the stem.
--rootedset_oneste_eachvertex_V defines rootedset,
--The stem is 1, so the forward order is defined in size_one_circuits_preorder.
--Is it actually easier to prove if you define the previous order directly from f?This is defined by transitive closure.
--The relationship is indicated by size_one_preorder_eq_transition.

instance (s : Setup α) : Preorder {x // x ∈ s.V} := s.pre

----------------------
--The part where Closure System is introduced from the setup definition.
-----------------------

--Create rootedset from setup.To create from f, you can use rootedset_onestem_eachvertex_V.Maybe you can include it in your setup.
--To make a binary relationship from --RootedSets, use R_from_RS1 to create a binary relationship from only stem size 1.
noncomputable def rootedset_from_setup {α : Type} [Fintype α] [DecidableEq α] (s: Setup α) : RootedSets α :=
 rootedset_onestem_eachvertex_V s.V s.f s.valid s.nonemp

lemma rootedset_from_setup_ground (s:Setup α) :
  (rootedset_from_setup s).ground = s.V :=
by
  rfl

--All stem sizes of the RootedSets at this time must be 1.
lemma rootedsetset_from_setup_has_stem1 (s: Setup α) :
 ∀ p ∈ (rootedset_from_setup s).rootedsets, p.stem.card = 1 :=
by
  dsimp [rootedset_from_setup]
  dsimp [rootedset_onestem_eachvertex_V]
  intro p hp
  rw [Finset.mem_image] at hp
  obtain  ⟨a, ha⟩ := hp
  rw [←ha.2]
  simp

--A function that gives ClosureSystem when you give setup.
--There is also a way to define it as pre_closuresystem2 below.
--I thought it would be better to move the definition into functionalTreeIdeal, but it's necessary to state the main theorem.
--Like I'm here.
noncomputable def pre_closuresystem (s:Setup α): ClosureSystem α :=
{
  ground := s.V
  sets := fun ss : Finset α => ss ⊆ s.V ∧(∀ v : s.V, v.val ∈ ss → (∀ w : s.V, s.pre.le w v → w.val ∈ ss)),
  inc_ground:= by
    intro ss a
    exact a.1
  nonempty_ground := by
    exact s.nonemp
  has_ground := by
    --simp_all only
    constructor
    · simp_all only [subset_refl]
    ·
      intro v a a_1
      intro a_2
      simp_all only [coe_mem]
  intersection_closed := by
    intro s t a b
    --simp_all only
    constructor
    ·
      obtain ⟨left, right⟩ := a
      obtain ⟨left_1, right_1⟩ := b
      intro v hv
      simp_all only [Finset.mem_inter]
      obtain ⟨left_2, right_2⟩ := hv
      simp_all only [Subtype.forall]
      apply left_1
      simp_all only
    ·
      intro v a_1 w a_2
      simp_all only [Subtype.forall, Finset.mem_inter]
      obtain ⟨val, property⟩ := v
      obtain ⟨val_1, property_1⟩ := w
      obtain ⟨left, right⟩ := a
      obtain ⟨left_1, right_1⟩ := b
      obtain ⟨left_2, right_2⟩ := a_1
      simp_all only
      apply And.intro
      · tauto
      · tauto
}

--Aggregation families are defined separately via rootedcircutures.Equivalence is denoted by ideal_system_eq_lem.
--Use in functionalMain.
noncomputable def pre_closuresystem2 (s:Setup α): ClosureSystem α :=
 rootedsetToClosureSystem (rootedset_from_setup s)
--They are defined using existing functions, but the rootedsetToClosureSystem is complicated so it may not be easy.

--Will preorderidealsytem equal rootedsetToClosureSystem(rootedset_onestem_eachvertex_V)?
--Can we prove it by using existing theorems?Find the theorem for the relationship between rootedToClosureSystem and ideal.
--If the stem size of the representation is all 1, then the set family created from RS and the preorder created from stem 1 match.
--lemma size_one_preorder_lemma {α : Type} [DecidableEq α] [Fintype α]
--  (RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
--  (h₁ : ∀ p ∈ RS.rootedsets, p.stem.card = 1) :
--  let SF := rootedsetToClosureSystem RS
--  ∀ s : Finset RS.ground, SF.sets (s.image Subtype.val) ↔ (s ∈ (preorder.S_R (R_from_RS1 RS))) :=

--I'm using it at the back.
lemma subtype_subset_attach {α : Type} (ss t : Finset α)  :
    Finset.subtype (fun x => x ∈ t) ss ⊆ t.attach :=
by
  intro x hx
  simp_all only [mem_subtype, mem_attach]

-- The relationship between the size and size of the relationship and the preorder defined by the sleep circuit.
-- Both facing.Is it the same as size_one_preorder_setup_lemma?
private lemma le_eq_R (s : Setup α) (x y : {x // x ∈ s.V}) :
  s.pre.le y x ↔ preorder.R_hat (R_from_RS1 (rootedset_from_setup s)) x y :=
by
  apply Iff.intro
  · intro hxy
    rw [s.h_pre] at hxy
    dsimp [size_one_preorder] at hxy
    dsimp [size_one_circuits_preorder] at hxy
    dsimp [rootedset_from_setup]
    exact hxy
  · intro hxy
    rw [s.h_pre]
    dsimp [size_one_preorder]
    dsimp [size_one_circuits_preorder]
    dsimp [rootedset_from_setup] at hxy
    exact hxy

--Indicates that the two definitions are equal.Essentially, what was shown in size_one_preorder_set.
--I was late to notice it, so the proof might be shorter.
--It is also used in the proof of the functionalMain's principal theorem.
lemma pre_closuresystem_eq_lem (s : Setup α) :
   pre_closuresystem s = pre_closuresystem2 s :=
by
  let sopl := size_one_preorder_lemma (rootedset_from_setup s)
  have :∀ p ∈ (rootedset_from_setup s).rootedsets, #p.stem = 1 :=
  by
    exact fun p a => rootedsetset_from_setup_has_stem1 s p a
  specialize sopl this
  simp at sopl
  dsimp [pre_closuresystem]
  dsimp [pre_closuresystem2  ]
  ext ss
  ·
    rfl
  · constructor
    · intro h
      have : ss ⊆ (rootedset_from_setup s).ground :=
      by
        exact h.1
      let ss_attach : Finset { x // x ∈ (rootedset_from_setup s).ground } :=
        ss.subtype (fun x => x ∈ (rootedset_from_setup s).ground)
      specialize sopl ss_attach
      have :(Finset.image Subtype.val ss_attach) = ss:=
      by
        ext y
        constructor
        · intro hh
          rw [Finset.mem_image] at hh
          simp at hh
          dsimp [ss_attach]
          dsimp [ss_attach] at hh
          obtain ⟨hh1,hh⟩ := hh
          rw [Finset.mem_subtype] at hh
          simp at hh
          exact hh
        · intro hh
          rw [Finset.mem_image]
          dsimp [ss_attach]
          simp
          constructor
          · exact hh
          · exact this hh

      rw [this] at sopl
      apply sopl.mpr
      dsimp [ss_attach]
      dsimp [preorder.S_R]
      dsimp [preorder.closedUnder]

      simp at h
      rw [s.h_pre] at h
      dsimp [size_one_preorder] at h
      dsimp [size_one_circuits_preorder] at h
      dsimp [rootedset_from_setup]
      dsimp [preorder.R_hat] at h
      dsimp [preorder.S_R] at h
      dsimp [preorder.closedUnder] at h
      simp at h
      simp
      obtain ⟨h1,h2⟩ := h

      constructor
      · -- (rootedset_onestem_eachvertex_V s.V s.f ⋯ ⋯).
        suffices Finset.subtype (fun x => x ∈ s.V) ss ⊆ s.V.attach from by
          exact this
        let ssa := subtype_subset_attach ss s.V
        convert ssa

      · intro w1 hw1 w2 hw2 hh whh1
        specialize h2 w1 hw1 whh1
        specialize h2 w2 hw2
        apply h2
        intro s2 hs2 hhs2 hhhs2
        exact hhs2 w1 hw1 w2 hw2 hh hhhs2

    · intro h
      have hsub : ss ⊆ (rootedset_from_setup s).ground :=
      by
        dsimp [rootedset_from_setup]
        dsimp [rootedset_onestem_eachvertex_V]
        have :(rootedsetToClosureSystem (rootedset_from_setup s)).ground = s.V :=
        by
          rfl
        exact (rootedsetToClosureSystem (rootedset_from_setup s)).inc_ground ss h

      let ss_attach : Finset {x // x ∈ (rootedset_from_setup s).ground} :=
        ss.subtype (fun x => x ∈ (rootedset_from_setup s).ground)

      -- `Finset.image Subtype.val ss_attach = ss`
      have himg : Finset.image Subtype.val ss_attach = ss := by
        ext x
        constructor
        · intro hx
          rw [Finset.mem_image] at hx
          simp at hx
          obtain ⟨w,hx⟩ := hx
          dsimp [ss_attach] at hx
          simp_all only [mem_subtype, ss_attach]
        · intro hx
          simp_all only [attach_image_val, ss_attach]
          rw [Finset.mem_image]
          simp
          constructor
          · exact hx
          · exact hsub hx

      have hS : ss_attach ∈ preorder.S_R (R_from_RS1 (rootedset_from_setup s)) := by
        dsimp [ss_attach]
        show Finset.subtype (fun x => x ∈ (rootedset_from_setup s).ground) ss ∈ preorder.S_R (R_from_RS1 (rootedset_from_setup s))

        have hsets :
          (rootedsetToClosureSystem (rootedset_from_setup s)).sets
            (Finset.image Subtype.val ss_attach) := by
           simpa [himg] using h
        exact (sopl ss_attach).mp hsets


      constructor
      · exact hsub
      · intro w1 hw1 w2 hw2
        dsimp [preorder.S_R] at hS
        rw [Finset.mem_filter] at hS
        dsimp [preorder.closedUnder] at hS
        have eq_ground:(rootedset_from_setup s).ground = s.V :=
        by
          exact rfl
        obtain ⟨hS1,hS2⟩ := hS

        have hS2':  ∀ ⦃x y : { x // x ∈ s.V}⦄,
           R_from_RS1 (rootedset_from_setup s) x y → x ∈ ss_attach → y ∈ ss_attach :=
        by
          intro x y
          intro a a_1
          simp_all only [Finset.mem_powerset, mem_subtype, Subtype.forall, ss_attach]
          simp_all only [ss_attach]
          obtain ⟨val_2, property_2⟩ := x
          obtain ⟨val_3, property_3⟩ := y
          tauto

        have hR :  preorder.R_hat (R_from_RS1 (rootedset_from_setup s)) w1 w2 :=
        by
          exact (le_eq_R s w1 w2).mp hw2

        -- 2.  w1 ∈ ss_attach
        have hw1_in : (w1 : {x // x ∈ s.V}) ∈ ss_attach := by
          have : (w1 : α) ∈ ss := hw1
          have hground : (w1 : α) ∈ s.V := w1.property
          simp_all only [Finset.mem_powerset, mem_subtype, Subtype.forall, coe_mem, ss_attach]

        dsimp [rootedset_from_setup] at hS2'
        have ideal_eq_ss :preorder_ideal (rootedset_from_setup s) ss_attach = Finset.subtype (fun x => x ∈ s.V) ss :=
        by
          have hsubs : ss_attach =
              Finset.subtype (fun x : α => x ∈ s.V) ss :=
          by
            exact rfl

          rw [←hsubs]
          show (preorder_ideal (rootedset_from_setup s)) ss_attach = ss_attach

          rw [←himg] at h
          let sops := size_one_preorder_set (rootedset_from_setup s) (rootedsetset_from_setup_has_stem1 s) ss_attach h
          exact sops

        let RS := rootedset_from_setup s
        have : (w2 : α) ∈ ss := by
          have hw1_ideal : w1 ∈ preorder_ideal RS ss_attach := by
            have hw1_attach : w1 ∈ ss_attach := hw1_in
            have : (w1 : α) ∈ RS.ground := w1.property

            simp_all only [Finset.mem_powerset, mem_subtype, Subtype.forall, coe_mem, ss_attach, RS]

          have hw2_ideal :=
            preorder_ideal_closed_lemma (RS := RS) (s := ss_attach)
              w1 w2 hR hw1_ideal

          simp_all only [Finset.mem_powerset, mem_subtype, Subtype.forall, RS, ss_attach]

        exact this

------------------------------------------------------------------------------------------------------------------
--Relationship of equivalence classes related to Setup.Setoid is installed in Setup, but it doesn't use setoid, perhaps because it was created before that.

--I'm using it below.In the Setup framework, all equal elements are given.
noncomputable def eqClass_setup (s: Setup α) (x : {x : α // x ∈ s.V}) : Finset {x // x ∈ s.V} :=
  s.V.attach.filter (fun y => s.setoid.r x y)

--Elements that have the same equivalent value have a relationship of size.
lemma eqClass_le (s: Setup α) : (x y: {x : α // x ∈ s.V}) → y ∈ eqClass_setup s x → s.pre.le x y :=
by
  intro x y h
  simp [eqClass_setup] at h
  rw [s.h_setoid] at h
  simp_all only [AntisymmRel.setoid_r]
  obtain ⟨val, property⟩ := x
  obtain ⟨val_1, property_1⟩ := y
  exact h.1

--The above reverse direction.
lemma eqClass_ge (s: Setup α) : (x y: {x : α // x ∈ s.V}) → y ∈ eqClass_setup s x → s.pre.le y x :=
by
  intro x y h
  simp [eqClass_setup] at h
  rw [s.h_setoid] at h
  simp_all only [AntisymmRel.setoid_r]
  obtain ⟨val, property⟩ := x
  obtain ⟨val_1, property_1⟩ := y
  exact h.2

--Conversely, if the value is the same in the previous order, it is also the same in eqClass.Despite its eq, it is not a necessary and sufficient condition.
lemma eqClass_lem (s: Setup α) : (x y: {x : α // x ∈ s.V}) → s.pre.le x y →s.pre.le y x → eqClass_setup s x = eqClass_setup s y :=
by
  intro x y hxy hyx
  ext z
  apply Iff.intro
  ·
    simp [eqClass_setup]
    rw [s.h_setoid]
    simp_all only [AntisymmRel.setoid_r]
    dsimp [AntisymmRel]
    intro h
    constructor
    · exact LE.le.trans_antisymmRel hyx h

    · exact AntisymmRel.trans_le (id (And.symm h)) hxy
  ·
    simp [eqClass_setup]
    rw [s.h_setoid]
    simp_all only [AntisymmRel.setoid_r]
    obtain ⟨xval, xproperty⟩ := x
    obtain ⟨yval, yproperty⟩ := y
    dsimp [AntisymmRel]
    intro h
    constructor
    ·
      exact s.pre.le_trans ⟨xval, xproperty⟩ ⟨yval, yproperty⟩ z hxy h.1
    ·
      exact s.pre.le_trans z ⟨yval, yproperty⟩ ⟨xval, xproperty⟩ h.2 hyx

--I haven't used it but I made it later.
lemma eqClass_xy (s: Setup α)  (x y: {x : α // x ∈ s.V}) :
 x ∈ eqClass_setup s y ↔ y ∈ eqClass_setup s x :=
by
  constructor
  · intro h
    simp [eqClass_setup] at h
    dsimp [eqClass_setup]
    rw [Finset.mem_filter]
    constructor
    · exact mem_attach s.V y
    · exact id (Setoid.symm' s.setoid h)
  · intro h
    simp [eqClass_setup] at h
    dsimp [eqClass_setup]
    rw [Finset.mem_filter]
    constructor
    · exact mem_attach s.V x
    · exact id (Setoid.symm' s.setoid h)

--I made it because of necessity.Equivalent elements are equal in the previous order.
lemma eqClass_lem_rev (s: Setup α) : (x y z: {x : α // x ∈ s.V}) → x ∈ eqClass_setup s z → y ∈ eqClass_setup s z → s.pre.le x y ∧ s.pre.le y x:=
by
  intro x y z hx hy
  constructor
  · dsimp [eqClass_setup] at hx
    dsimp [eqClass_setup] at hy
    rw [s.h_setoid] at hx hy
    simp_all only [AntisymmRel.setoid_r]

    simp_all only [mem_filter, mem_attach, true_and]
    rw [AntisymmRel] at hx hy
    obtain ⟨left, right⟩ := hx
    obtain ⟨left_1, right_1⟩ := hy
    exact right.trans left_1
  · dsimp [eqClass_setup] at hx
    dsimp [eqClass_setup] at hy
    rw [s.h_setoid] at hx hy
    simp_all only [AntisymmRel.setoid_r]
    simp_all only [mem_filter, mem_attach, true_and]
    rw [AntisymmRel] at hx hy
    obtain ⟨left, right⟩ := hx
    obtain ⟨left_1, right_1⟩ := hy
    apply Preorder.le_trans
    assumption
    simp_all only

--I'm not using it directly now, but I created it as a summary of the theorem above.
lemma eqClass_eq (s: Setup α) (x y: {x : α // x ∈ s.V}) :
  y ∈ eqClass_setup s x ↔ (s.pre.le x y ∧ s.pre.le y x) :=
by
  constructor
  · intro h
    simp [eqClass_setup] at h
    rw [s.h_setoid] at h
    simp_all only [AntisymmRel.setoid_r]
    dsimp [AntisymmRel]
    obtain ⟨left, right⟩ := h
    constructor
    · exact left
    · exact right
  · intro h
    simp [eqClass_setup]
    rw [s.h_setoid]
    simp_all only [AntisymmRel.setoid_r]
    dsimp [AntisymmRel]
    constructor
    · exact h.1
    · exact h.2

---
--Parts that are not directly related to Setup.It's more abstract.

def reach {A : Type} (f : A → A) (x y : A) : Prop :=
  ∃ n : ℕ, f^[n] x = y

lemma reach_trans {A : Type} (f : A → A) {x y z : A}
  (hxy : reach f x y) (hyz : reach f y z) :
  reach f x z := by
  obtain ⟨n, hn⟩ := hxy
  obtain ⟨m, hm⟩ := hyz
  exists (n + m)
  subst hn hm
  rw [←Function.iterate_add_apply]
  rw [add_comm]
