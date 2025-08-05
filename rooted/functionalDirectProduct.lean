import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
--import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.functionalPartialMaximal
import rooted.functionalPartialTrace

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

-- One of the equivalence classes is used as q and divided into the q side and the part other than q.
--Set the sum of the magnitudes of one order ideal as s1, the number of order ideal as h1, and the size of the vertex set is n1.
--Set the sum of the magnitudes of the other order ideals as s2, the number of order ideals as h2, and the size of the vertex set as n2.
-- The sum of the magnitudes of the order ideal for the combined partial order set is s1*h2+s2*h1.
--The number of ordered ideals for the combined partial order set is h1*h2.
--The size of the platform set of the combined partially ordered set is n1+n2.
--To be average rare, (s1*h2+s2*h1)*2-(h1*h2)*(n1+n2)<=0.
-- Since each is averaged, this is true since s1*2-h1*n1<=0, s2*2-h2*n2<=0.
--If there are three or more connected components, they will be proven by induction.

-- First, define the part that is neither comp nor excl.

--- Number of connected components.But this is what it was when setoid gave it.Should I change the location?
def numClasses {α : Type _} (st : Setoid α)
  [Fintype α] [DecidableEq (Quotient st)] : ℕ :=
  (Finset.univ.image (Quot.mk st.r)).card
--The number of connected components must be 1 or more.
--Reference available from Main.
lemma numClasses_pos (s : Setup_po α) :
  (numClasses (proj_setoid s)) > 0 := by
  dsimp [numClasses]

  have h1 : Fintype.card (Quotient (proj_setoid s)) ≥ 1 := by
    let qx := Quot.mk (proj_setoid s)
    obtain ⟨x, h_nonemp⟩ := Setup_po.nonemp s
    specialize qx ⟨x, h_nonemp⟩
    simp_all only [ge_iff_le]
    apply Fintype.card_pos_iff.mpr
    exact Nonempty.intro qx

  simp_all only [ge_iff_le, gt_iff_lt, card_pos, Finset.image_nonempty, attach_nonempty_iff]
  cases s
  simp_all only

--There is a reference there.
lemma quotient_exists (s : Setup_po α) :
Nonempty (Quotient (proj_setoid s)) := by

  obtain ⟨v, hv⟩ := Setup_po.nonemp s
  let x := Quotient.mk (proj_setoid s) ⟨v, hv⟩
  use x

-- Number of connected components.Define for setup_po.Same as numClasses, but revived if necessary.
--noncomputable def num_connected_components (s : Setup_po α) : ℕ :=
-- (Finset.univ.image (Quot.mk (proj_setoid s))).card
-- It may be defined as numClasses (proj_setoid s).

--Is this not the comp side or excl side?
noncomputable def  restrict_order_core
  (s : Setup_po α)
  (V' : Finset α)
  (sub : V' ⊆ s.V) :
  PartialOrder (Subtype fun x => x ∈ V') :=
{ le            := fun x y =>
    -- compare via the original order on s.V
    s.po.le ⟨x.1, sub x.2⟩ ⟨y.1, sub y.2⟩
, le_refl       := fun x =>
    -- reflexivity from the original order
    s.po.le_refl _
, le_trans      := fun {x y z} hxy hyz =>
    -- transitivity from the original order
    s.po.le_trans ⟨x.1, sub x.2⟩ ⟨y.1, sub y.2⟩ ⟨z.1, sub z.2⟩ hxy hyz
, le_antisymm  := fun {x y} hxy hyx => by
    -- antisymmetry from the original order, then Subtype.ext to lift to the subtype
    let sp := s.po.le_antisymm ⟨x.1, sub x.2⟩ ⟨y.1, sub y.2⟩ hxy hyx
    apply Subtype.ext
    simpa using sp
}
-------------------------------
---Here is the definition of the comp.
-------------------------------

-- A set of vertices on the q side.This is a subtyped comp_po_V'
noncomputable def compFinset (s : Setup_po α) (q : Quotient (proj_setoid s))[DecidableEq (Quotient (proj_setoid s))] : Finset {x // x ∈ s.V} :=
  Finset.filter (fun (v:{x // x ∈ s.V}) => @Quotient.mk'' _ (proj_setoid s) v = q) s.V.attach

-- The partial order restricted to the q side
noncomputable def  restrict_order_comp (s : Setup_po α) (q : Quotient (proj_setoid s)) : PartialOrder ((compFinset s q).image Subtype.val) :=
let V := (compFinset s q).image Subtype.val
have sub: V ⊆ s.V := by
      simp_all only [coe_mem, V]
      rw [Finset.image_subset_iff]
      intro x a
      simp_all only [coe_mem, V]
{

  le := fun (x:V) (y:V) =>

    have xin : x.val ∈ s.V := by
      simp_all only [V]
      exact sub x.property
    have yin : y.val ∈ s.V := by
      simp_all only [V]
      exact sub y.property

    s.po.le ⟨x.val,xin⟩ ⟨y.val,yin⟩

  le_refl := by
    intro a
    simp_all only [le_refl, V]

  le_antisymm := by
    intros x y hxy hyx
    have xin : x.val ∈ s.V := by
      simp_all only [coe_mem, V]
      exact sub x.property
    have yin : y.val ∈ s.V := by
      simp_all only [coe_mem, V]
      exact sub y.property
    let spl := s.po.le_antisymm ⟨x.val, xin⟩ ⟨y.val, yin⟩ hxy hyx
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    simp_all only [Subtype.mk.injEq, V]
    simpa using spl

  le_trans := by
    intros x y z hxy hyz
    have xin : x.val ∈ s.V := by
      exact sub x.property
    have yin : y.val ∈ s.V := by
      exact sub y.property
    have zin : z.val ∈ s.V := by
      exact sub z.property
    exact s.po.le_trans ⟨x.val, xin⟩ ⟨y.val, yin⟩ ⟨z.val, zin⟩ hxy hyz
}



--variable {α : Type} [Fintype α] [DecidableEq α]

--First, prepare the component on the comp side (the side consisting of q).

--V' definition is top level.A subtyped compFinset.
noncomputable def comp_po_V' (s : Setup_po α) (q : Quotient (proj_setoid s)) : Finset α :=
  (compFinset s q).image Subtype.val

-- V' ⊆ s.V proof at top level
private lemma comp_po_sub (s : Setup_po α) (q : Quotient (proj_setoid s)) :
  comp_po_V' s q ⊆ s.V := by
  dsimp [comp_po_V'];
  simp [Finset.image_subset_iff]

-- New transition function f restricted within q.
noncomputable def comp_po_f
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (v' : comp_po_V' s q) : comp_po_V' s q := by
  have vin : v'.val ∈ s.V := comp_po_sub s q v'.property

  let fv : s.V := s.f ⟨v'.val, vin⟩

  have hq :  q = Quotient.mk (proj_setoid s) fv := by

      obtain ⟨w, hw⟩ := Quot.exists_rep q
      calc
        q
          = Quotient.mk _ w := Eq.symm hw
        _ = Quotient.mk _ ⟨v'.1, vin⟩ := by
          let vp := v'.property
          dsimp [comp_po_V'] at vp
          rw [Finset.mem_image] at vp
          simp at vp
          obtain ⟨w, hwf⟩ := vp
          rename_i w_1
          subst hw
          dsimp [compFinset] at hwf
          rw [Finset.mem_filter] at hwf
          simp_all only [mem_attach, true_and]
          obtain ⟨val, property⟩ := w_1
          obtain ⟨val_1, property_1⟩ := v'
          obtain ⟨val_2, property_2⟩ := fv
          simp_all only
          rfl

        _ = Quotient.mk _ fv := by
          apply Quot.sound
          dsimp [projr];
          apply po_maximal_reachable_eq s ⟨v'.1, vin⟩-- (proj_max s v') (proj_max s fv)
          · constructor
            · -- reach s.f (s.f v') (proj_max s fv)
              obtain ⟨x₀, hmp, ⟨k, hk⟩⟩ := po_maximal_reachable s fv
              intro y hy
              have : po_maximal s (proj_max s ⟨↑v', vin⟩) :=
              by
                exact proj_max_maximal s ⟨↑v', vin⟩
              dsimp [po_maximal] at this
              specialize this y hy
              exact this

            · -- reach s.f v' (proj_max s v')
              obtain ⟨x₁, hmp₁, ⟨k, hk₁⟩⟩ := po_maximal_reachable s ⟨v'.1, vin⟩
              dsimp [reach]
              use k
              rw [hk₁]
              show  x₁ = proj_max s ⟨↑v', vin⟩
              have :reach s.f ⟨↑v', vin⟩  x₁ :=
              by
                dsimp [reach]
                use k
              let pm := proj_max_unique s ⟨hmp₁, this⟩
              symm
              exact pm
          · constructor
            · -- proj_max s (s.f v') = proj_max s v'
              obtain ⟨x₀, hmp, ⟨k, hk⟩⟩ := po_maximal_reachable s fv
              dsimp [po_maximal] at hmp
              exact proj_max_maximal s fv

            · -- reach s.f v' (proj_max s v')
              obtain ⟨x₁, hmp₁, ⟨k, hk₁⟩⟩ := po_maximal_reachable s ⟨v'.1, vin⟩
              dsimp [reach]
              use k
              rw [hk₁]
              have :reach s.f ⟨↑v', vin⟩  x₁ :=
              by
                dsimp [reach]
                use k
              have :reach s.f (s.f ⟨↑v', vin⟩)  x₁ :=
              by
                dsimp [reach]
                use k-1
                rw [←@Function.comp_apply _ _ _ s.f^[k - 1]  ]
                rw [←Function.iterate_succ]
                by_cases hk:k = 0
                case pos =>
                  rw [hk] at hk₁
                  simp at hk₁
                  rw [hk₁]
                  rw [hk ]
                  simp
                  exact (po_maximal_lem s x₁).mp hmp₁
                case neg =>
                  have : (k - 1).succ = k := by
                    exact Nat.succ_pred_eq_of_ne_zero hk
                  subst hw hk₁
                  simp_all only [Nat.succ_eq_add_one]

              let pm := proj_max_unique s ⟨hmp₁, this⟩
              symm
              dsimp [fv]
              exact pm

  refine ⟨fv.1, by
    dsimp [comp_po_V']; dsimp [compFinset]
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right,
      exists_eq_right, Subtype.coe_eta, coe_mem, exists_const]
    simp [compFinset]
    rfl⟩

--Move the subtyped point to s.V.
def comp_po_to_sV
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (v' : comp_po_V' s q) : s.V :=
⟨ v'.val, comp_po_sub s q v'.2 ⟩

--Lema 1: The original s.f matches the restricted comp_po_f.
--I'm using it below.
private lemma comp_po_iter_val
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (x : comp_po_V' s q) :
  ∀ n : ℕ, (((comp_po_f s q)^[n]) x).val = (s.f^[n]) ⟨x, comp_po_sub s q x.2⟩ := by

  intro n
  induction n with
  | zero =>
    simp only [Function.iterate_zero]
    simp_all only [id_eq]
  | succ n ih =>
    rw [Function.iterate_succ']
    rw [Function.iterate_succ']
    rw [Function.comp_apply]
    rw [Function.comp_apply]
    have xin: x.val ∈ s.V := by
      let xp := x.property
      dsimp [comp_po_V'] at xp
      rw [Finset.mem_image] at xp
      simp at xp
      dsimp [compFinset] at xp
      simp at xp
      obtain ⟨w, hwf⟩ := xp
      exact w

    have h_eq : ((comp_po_f s q)^[n]) x = (s.f^[n] ⟨x,xin⟩).val :=
    by
      simp_all only

    obtain ⟨val, property⟩ := x
    simp_all only
    simp only [comp_po_f, h_eq]

-- 補題2:ReachGXY ↔ReachSFSxSy
private lemma comp_po_reach_equiv
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (x y : comp_po_V' s q) :
  reach (comp_po_f s q) x y
    ↔ reach s.f ⟨x, comp_po_sub s q x.2⟩ ⟨y, comp_po_sub s q y.2⟩ :=
by

  let sx : { a // a ∈ s.V } := ⟨x, comp_po_sub s q x.2⟩
  let sy : { a // a ∈ s.V } := ⟨y , comp_po_sub s q y.2⟩
  constructor
  ·
    intro ⟨n, hn⟩; use n
    have h_iter := comp_po_iter_val s q x n
    have h₁ : ((comp_po_f s q)^[n] x).val = y.val := congrArg Subtype.val hn
    have h₂ : (s.f^[n] sx).val = y.val := by
      rw [h_iter] at h₁; exact h₁
    apply Subtype.ext; exact h₂

  ·
    intro ⟨n, hn⟩; use n
    have h_iter := comp_po_iter_val s q x n
    have h₁ : (s.f^[n] sx).val = sy.val := congrArg Subtype.val hn
    have h₂ : ((comp_po_f s q)^[n] x).val = y.val := by
      rw [←h_iter] at h₁; exact h₁
    apply Subtype.ext; exact h₂

--Lema 3: Expanding restrict_order_comp.le.Relationship between original and limited half orders
@[simp]
private lemma comp_po_restrict_le_iff
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (x y : comp_po_V' s q) :
  ( restrict_order_comp s q).le x y ↔ s.po.le ⟨x, comp_po_sub s q x.2⟩ ⟨y, comp_po_sub s q y.2⟩ := by
  simp [restrict_order_comp]


-- Definition of Setup_po restricted to q
noncomputable def comp_po (s : Setup_po α) (q : Quotient (proj_setoid s))
  : Setup_po α :=
{ V      := comp_po_V' s q,
  nonemp := by
    obtain ⟨v, hv⟩ := Quot.exists_rep q
    have hv_mem : v ∈ compFinset s q := by
      dsimp [compFinset]
      subst hv
      simp_all only [mem_filter, mem_attach, true_and]
      obtain ⟨val, property⟩ := v
      rfl
    refine ⟨Subtype.val v, Finset.mem_image.2 ⟨v, hv_mem, rfl⟩⟩
, f      := comp_po_f s q
, po     :=  restrict_order_comp s q
, order  := fun x y => by
    simpa [comp_po_restrict_le_iff s q, ← comp_po_reach_equiv s q x y]
      using (comp_po_reach_equiv s q x y).trans (s.order _ _) }

------------------------------
--The part used to define partial order excluding q.excl side.
-------------------------------

-- Definition of vertex sets excluding q.Subtyped.
noncomputable def exclFinset
  (s : Setup_po α) (q : Quotient (proj_setoid s))[DecidableRel (projr s)]  :
  Finset {x // x ∈ s.V} :=
  Finset.filter
    (fun v ↦ @Quotient.mk _ (proj_setoid s) v ≠ q)
    s.V.attach

/-- Vertex set of Finset α in the excluded part -/
noncomputable def excl_po_V'
  (s : Setup_po α)
  (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)]
  [DecidableEq (Quotient (proj_setoid s))] :
  Finset α :=
  (exclFinset s q).image Subtype.val

--Lemma where exclFinset is the whole subset.
private lemma excl_po_sub
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)]
  [DecidableEq   (Quotient (proj_setoid s))] :
  excl_po_V' s q ⊆ s.V := by
  dsimp [excl_po_V', exclFinset]
  simp only [Finset.image_subset_iff, Subtype.coe_mk]
  intros x hx
  exact coe_mem x

--Definition of a function that gives the vertex of the parent on the excl side.
noncomputable def excl_po_f
  (s : Setup_po α)
  (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)]
  [DecidableEq (Quotient (proj_setoid s))]
  (v' : excl_po_V' s q) :
  excl_po_V' s q := by

  have hv : (v' : α) ∈ s.V := excl_po_sub s q v'.property
  let fv : s.V := s.f ⟨v', hv⟩
  let v  : s.V := ⟨v', hv⟩

  let mk : s.V → Quotient (proj_setoid s) := @Quotient.mk s.V (proj_setoid s)

  let spec_fv := proj_max_spec s fv

  have reach_v_fv : reach s.f v fv := by
    use 1
    simp
    simp_all only [v, fv]

  have reach_v_pm : reach s.f v (proj_max s fv) := by

    let rsv := reach_maximal s fv--reach_v_fv spec_fv.2
    exact reach_trans s.f reach_v_fv rsv

  have h1 : po_maximal s (proj_max s fv) ∧ reach s.f v (proj_max s fv) :=
    ⟨spec_fv.1, reach_v_pm⟩

  let spec_v := proj_max_spec s v

  let eq_pm := po_maximal_reachable_eq s v (proj_max s fv) (proj_max s v) h1 spec_v

  have cls : mk fv = mk v := by
    apply Quot.sound; exact eq_pm

  have v_neq_q : (Quotient.mk (proj_setoid s) v) ≠ q := by

    let vp := v'.property
    dsimp [excl_po_V'] at vp
    dsimp [exclFinset] at vp
    rw [Finset.mem_image] at vp
    simp at vp
    obtain ⟨w, hwf⟩ := vp
    exact hwf

  have hneq : (Quotient.mk (proj_setoid s) fv) ≠ q := by
    intro heq
    have : (Quotient.mk _ v) = q := by calc
      _ = _ := (cls.symm)
      _ = _ := heq

    exact (v_neq_q this)

  have fv_in : fv ∈ exclFinset s q := by
    dsimp [exclFinset]; simp [hneq]
  refine ⟨fv.1, by simpa [excl_po_V'] using fv_in⟩

-- The relationship between excl_po_f and normal s.f.1 step edition.
private lemma excl_po_val_step
  (s : Setup_po α) (q : Quotient (proj_setoid s))[DecidableRel (projr s)] [DecidableEq (Quotient (proj_setoid s))]
  (v : excl_po_V' s q) :
  (excl_po_f s q v).val
    = s.f ⟨v.val, excl_po_sub s q v.property⟩ := by
  dsimp [excl_po_f]

-- 2. Lemma n step edition where iteration values match before and after limit
private lemma excl_po_iter_val
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)] [DecidableEq (Quotient (proj_setoid s))]
  (x : excl_po_V' s q) :
  ∀ n : ℕ,
    ((excl_po_f s q)^[n] x).val
      = (s.f^[n]) ⟨x.val, excl_po_sub s q x.property⟩ := by
  intro n
  induction n with
  | zero =>
      simp [Function.iterate_zero]
  | succ n ih =>
      simp [Function.iterate_succ,excl_po_val_step,ih]
      have step : (excl_po_f s q ((excl_po_f s q)^[n] x)).val
            = s.f ⟨((excl_po_f s q)^[n] x).val, excl_po_sub s q ((excl_po_f s q)^[n] x).property⟩ :=
        excl_po_val_step _ _ _

      have ih_val :
        ((excl_po_f s q)^[n] x).val
          = ((s.f^[n]) ⟨x.val, excl_po_sub s q x.property⟩).val :=
      by
        simp_all only [Subtype.coe_eta]
      calc
        (((excl_po_f s q)^[n+1]) x).val
            = (excl_po_f s q ((excl_po_f s q)^[n] x)).val :=
        by
          rw [Function.iterate_succ']
          rw [Function.comp_apply]
        _ = s.f ⟨((excl_po_f s q)^[n] x).val, _⟩               := step
        _ = s.f ((s.f^[n]) ⟨x.val, _⟩)                         := by
          congr;
        _ = (s.f^[n+1]) ⟨x.val, excl_po_sub s q x.property⟩    := by
          rw [Function.iterate_succ']
          rw [Function.comp_apply]

-- Equivalence of reach before and after limiting excl
--References available from below.
private lemma excl_po_reach_equiv
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)] [DecidableEq (Quotient (proj_setoid s))]
  (x y : excl_po_V' s q) :
  reach (excl_po_f s q) x y
    ↔
  reach s.f
        ⟨x.val, excl_po_sub s q x.property⟩
        ⟨y.val, excl_po_sub s q y.property⟩ := by

  let sx : s.V := ⟨x.val, excl_po_sub s q x.property⟩
  let sy : s.V := ⟨y.val, excl_po_sub s q y.property⟩

  constructor
  ·
    rintro ⟨n, hn⟩

    have h_val : ((excl_po_f s q)^[n] x).val = y.val :=
      congrArg Subtype.val hn

    have h_val' : (s.f^[n] sx).val = y.val := by
      simpa [excl_po_iter_val s q x n] using h_val

    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact h_val'
  ·
    rintro ⟨n, hn⟩

    have h_val : (s.f^[n] sx).val = sy.val :=
      congrArg Subtype.val hn

    have h_val' :
        ((excl_po_f s q)^[n] x).val = y.val := by
      have := (excl_po_iter_val s q x n).symm
      simp_all only [sx, sy]

    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact h_val'

--called from functionalDirectProduct2.
-- The vertex set of excl is not non-empty.
theorem excl_po_V'_nonempty_of_classes_ge2
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)][DecidableEq (Quotient (proj_setoid s))]:
  (s.V.attach.image (Quot.mk (proj_setoid s))).card ≥ 2 →
  (excl_po_V' s q).Nonempty := by

  intro h

  have h1 : 1 < (s.V.attach.image (Quot.mk (proj_setoid s))).card := by
    simpa [Nat.succ_le_iff] using h

  obtain ⟨c, hc_mem, hc_ne⟩ :=
    exists_mem_ne h1 q

  obtain ⟨v, hv_attach, rfl⟩ := Finset.mem_image.mp hc_mem
  have v_ne : Quot.mk (proj_setoid s) v ≠ q := by simpa using hc_ne
  have hv_filter : v ∈ s.V.attach.filter fun v => Quot.mk _ v ≠ q := by
    dsimp [exclFinset]; simp [v_ne]
  have : Subtype.val v ∈ excl_po_V' s q := by
    dsimp [excl_po_V']; simp [hv_filter]
    simp_all only [ge_iff_le, mem_attach, Finset.mem_image, true_and, exists_apply_eq_apply, ne_eq, not_false_eq_true,
      mem_filter, and_self]
    obtain ⟨val, property⟩ := v
    simpa [exclFinset]
  exact ⟨v.val, this⟩

noncomputable def restrict_order_excl
  (s : Setup_po α)
  (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)]
  [DecidableEq   (Quotient (proj_setoid s))] :
  PartialOrder (excl_po_V' s q) :=
restrict_order_core s (excl_po_V' s q) (excl_po_sub s q)

--Excl side Setup_po definition.
--Should the nonempty assumption be replaced with two or more equivalence classes?
noncomputable def excl_po
  (s : Setup_po α) (q : Quotient (proj_setoid s))[DecidableRel (projr s)][DecidableEq (Quotient (proj_setoid s))]
  --(hnonempty : (excl_po_V' s q).Nonempty) :
  (geq2quotient: (numClasses (proj_setoid s) ≥ 2)) :
  Setup_po α :=
{ V       := excl_po_V' s q
, nonemp  := by
    have :#(Finset.image (Quot.mk ⇑(proj_setoid s)) s.V.attach) ≥ 2 := by
      dsimp [numClasses] at geq2quotient
      exact geq2quotient
    exact excl_po_V'_nonempty_of_classes_ge2 s q this
, f       := excl_po_f s q
, po      := restrict_order_excl s q
, order   := by
    intro x y

    let sx : s.V := ⟨x, excl_po_sub s q x.property⟩
    let sy : s.V := ⟨y, excl_po_sub s q y.property⟩


    have reach_equiv :
      reach (excl_po_f s q) x y ↔ reach s.f sx sy := by
      exact excl_po_reach_equiv s q x y

    have restr_iff :
      (restrict_order_excl s q).le x y ↔ s.po.le sx sy := by
      simp [restrict_order_excl]
      simp_all only [sx, sy]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      obtain ⟨val_2, property_2⟩ := sx
      obtain ⟨val_3, property_3⟩ := sy
      simp_all only
      rfl

    simpa [restr_iff] using (reach_equiv.trans (s.order sx sy)) }
