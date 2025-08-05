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
import rooted.functionalIdealrare
import rooted.functionalTraceIdeal

open Finset Set Classical

--The part that bridges the partial order structure Setup_po.
--The main point is to indicate that if the size of the equivalence class is all 1, it can be considered Setup_po.
--The excess part in the first half is connected in the form of 1 if exceed is 0.
--In the first half, you can either change the file name to functionalEqualOne or make it independent, or move it to TraceIdeal.
--However, here is also a discussion using exceed.
--For now, closuresystem will also appear in the second half, so we'll just leave it as is.
--For now,
--TraceIdeal Something that has something to do with Ideal and does not show any exces.
--functionalExcess What comes up with Excess.
--functionalSetuppo The part that results in Setup_so.
--It might be a good idea to reorganize it into --.

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

--It's simpler than just a Setup.There is no need to consider the equivalent class as in preorder.
structure Setup_po (α : Type) [Fintype α] [DecidableEq α] where
(V : Finset α)
(nonemp   : V.Nonempty)
(f : V → V)
(po : PartialOrder V)
(order : ∀ x y : V, (reach f x y ↔ po.le x y)) --fからpo.leが決まる。

def po_closuresystem {α : Type} [Fintype α] [DecidableEq α] (s: Setup_po α) : ClosureSystem α :=
{ ground := s.V,
  sets := fun ss : Finset α => ss ⊆ s.V ∧(∀ v : s.V, v.val ∈ ss → (∀ w : s.V, s.po.le w v → w.val ∈ ss)),
  inc_ground := by
    intro ss a
    exact a.1,
  has_ground := by
    simp
  nonempty_ground := by
    exact s.nonemp,
  intersection_closed := by
    intro s_1 t a a_1
    simp_all only [Subtype.forall, Finset.mem_inter, and_imp]
    obtain ⟨left, right⟩ := a
    obtain ⟨left_1, right_1⟩ := a_1
    apply And.intro
    · intro x hx
      simp_all only [Finset.mem_inter]
      obtain ⟨left_2, right_2⟩ := hx
      apply left left_2
    · intro a b a_1 a_2 a_3 b_1 a_4
      apply And.intro
      · tauto
      · tauto
}

--For Setup_pos with all magnitudes of 1, the corresponding Setup_pos can be defined.
--The group family of ideals coincides.

--Use it for the following definitions.Setup_po does not appear in the lemma.However, this may be a special constraint of 1 equivalent classification, so this might be fine.
private lemma class_size_one_implies_eq (s: Setup_spo α) (x y: s.V) (ssl  : (⟦x⟧ : Quotient s.setoid) = ⟦y⟧) (hq1x :#(Finset.filter (fun a => @Quotient.mk'' _ s.setoid a = ⟦x⟧) s.V.attach) = 1) (hq1y :#(Finset.filter (fun a => @Quotient.mk'' _ s.setoid a = ⟦y⟧) s.V.attach) = 1) :
     (x : α) = y := by
  have hcard :=
    (Finset.card_eq_one.mp hq1x)

  obtain ⟨xx, hxx_mem⟩ := hcard

  have hx_mem :
      (x : {a // a ∈ s.V}) ∈ Finset.filter (fun a => @Quotient.mk'' _ s.setoid a = ⟦x⟧) s.V.attach := by
    rw [Finset.mem_filter]
    simp_all only [Quotient.eq, mem_attach, and_self]


  have hy_mem :
      (y : {a // a ∈ s.V}) ∈ Finset.filter (fun a => @Quotient.mk'' _ s.setoid a = ⟦x⟧) s.V.attach := by
    rw [Finset.mem_filter]
    simp_all only [Quotient.eq, mem_attach, and_self]
    exact ⟨trivial, id (Setoid.symm' s.setoid ssl)⟩
  have heq: xx = x := by
    simp_all only [Quotient.eq, Finset.mem_singleton, mem_filter, mem_attach, true_and]
  have : xx = y := by
    subst heq
    simp_all only [Quotient.eq, Finset.mem_singleton]
  subst heq this
  simp_all only [Quotient.eq, Finset.mem_singleton, Finset.card_singleton]

--Definition of the partial order when you take a trace.
noncomputable def po_ideal_system_from_allone_le {α : Type} [Fintype α] [DecidableEq α] (s: Setup_spo α)  (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1): PartialOrder s.V :=
{
  le := fun (x y:s.V) => s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y),

  le_refl := by
    intro x
    exact s.spo.le_refl (@Quotient.mk s.V s.setoid x),

  le_trans := by
    intros x y z hxy hyz
    have sxy: s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) := by
      exact hxy
    have syz: s.spo.le (@Quotient.mk s.V s.setoid y) (@Quotient.mk s.V s.setoid z) := by
      exact hyz
    have sxz: s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid z) := by
      exact s.spo.le_trans (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) (@Quotient.mk s.V s.setoid z) sxy syz
    exact sxz,

  le_antisymm := by
    intros x y hxy hyx
    have sxy: s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) := by
      exact hxy
    have syx: s.spo.le (@Quotient.mk s.V s.setoid y) (@Quotient.mk s.V s.setoid x) := by
      exact hyx
    let ssl := s.spo.le_antisymm (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) sxy syx
    dsimp [classOf] at hq1
    let hq1x := hq1 (@Quotient.mk s.V s.setoid x)
    let hq1y := hq1 (@Quotient.mk s.V s.setoid y)

    let csoi := class_size_one_implies_eq s x y ssl hq1x hq1y
    exact Subtype.eq csoi
}

-- When hq1 holds, does it also indicate that there are all the equivalence class and elements, and that each of the reach corresponds to each other?
--In the end, it indicates that the relationship between large and small corresponds.

-- Lessons regarding when the magnitude of the equivalence class is 1.
lemma equal_one (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) (x y: s.V) :
  (@Quotient.mk s.V s.setoid x) = (@Quotient.mk s.V s.setoid y) ↔ x = y := by
  constructor
  · intro h
    have hcard := hq1 ⟦x⟧
    obtain ⟨z, hz_mem⟩ := Finset.card_eq_one.mp hcard
    have hx_mem : (x : {a // a ∈ s.V}) ∈ classOf s ⟦x⟧ := by
      exact classOf_self s x
    have hy_mem :
        (y : {a // a ∈ s.V}) ∈ classOf s ⟦x⟧ :=
    by
      have : (Quotient.mk'' y : Quotient s.setoid) = ⟦x⟧ := by
        exact id (Eq.symm h)
      simp [classOf, this]           -- membership registered
      simp_all only [Finset.card_singleton, Finset.mem_singleton, Quotient.eq]
    have hxz : (x : {a // a ∈ s.V}) = z := by simp_all only [Quotient.eq, Finset.card_singleton, Finset.mem_singleton] --huniq _ hx_mem
    have hyz : (y : {a // a ∈ s.V}) = z := by
      subst hxz
      simp_all only [Quotient.eq, Finset.card_singleton, Finset.mem_singleton] --huniq _ hy_mem
    subst hyz hxz
    simp_all only [Finset.card_singleton, Finset.mem_singleton]
  · intro h
    subst h
    simp_all only

-- Lessons regarding when the magnitude of the equivalence class is 1.
lemma equal_one2 (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) (x: s.V) :
   (@Quotient.mk _ s.setoid x).out = x :=
by
  let q : Quotient s.setoid := ⟦x⟧

  have hcard : (classOf s q).card = 1 := hq1 q
  obtain ⟨z, hz_mem⟩ := Finset.card_eq_one.mp hcard

  have hx_mem : (x : {a // a ∈ s.V}) ∈ classOf s q := by
    unfold classOf q
    simp [q]
    simp_all [q]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := z
    rfl

  have hout_mem :
      ((@Quotient.mk _ s.setoid x).out) ∈ classOf s q := by
    have hout_inV :
        ((@Quotient.mk _ s.setoid x).out) ∈ s.V.attach :=
    by
      simp_all only [Finset.mem_singleton, mem_attach, q]
    -- (b) `Quotient.mk'' out = ⟦x⟧`
    have hquot :
        (Quotient.mk'' ((@Quotient.mk _ s.setoid x).out)
          : Quotient s.setoid) = q := by
      -- `Quotient.out_eq` : `Quotient.mk'' (out q') = q'`
      have : (Quotient.mk'' ((@Quotient.mk _ s.setoid x).out)
                : Quotient s.setoid)
              = (@Quotient.mk _ s.setoid x) :=
      by
        simp_all only [Finset.mem_singleton, mem_attach, Quotient.out_eq, q]


      simp_all only [Finset.mem_singleton, mem_attach, Quotient.out_eq, q]
    unfold classOf q
    simp [hout_inV, hquot]
    exact (@Quotient.eq _ s.setoid ⟦x⟧.out x).mp hquot

  have hxz  : (x : {a // a ∈ s.V}) = z :=
  by
    simp_all only [Finset.mem_singleton, q]
  have houtz : ((@Quotient.mk _ s.setoid x).out) = z :=
  by
    subst hxz
    simp_all only [Finset.mem_singleton, q]

  subst hxz
  simp_all only [q]

--Lesma regarding when the magnitude of the equivalence class is 1.
private lemma equal_one_f (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) (x y: s.V) :
  s.fq (@Quotient.mk s.V s.setoid x) = (@Quotient.mk s.V s.setoid y) ↔ ((fun xx => s.fq (@Quotient.mk _ s.setoid xx)) x).out = y :=
by
  have h_eq₁ := equal_one s hq1 ((s.fq ⟦x⟧).out) y

  constructor
  · intro hq
    have : (Quotient.mk'' (s.fq ⟦x⟧).out : Quotient s.setoid) =
            (s.fq ⟦x⟧) := by
      simp_all only [Quotient.out_eq, true_iff]
    have hq' : (Quotient.mk'' (s.fq ⟦x⟧).out : Quotient s.setoid) = ⟦y⟧ := by
      simpa [this] using hq
    have : (s.fq ⟦x⟧).out = (y : α) :=
    by
      simp_all only [Quotient.out_eq, true_iff]
    simp_all only [Quotient.out_eq, true_iff]

  · intro hout

    have hout_q :
        (Quotient.mk'' (s.fq ⟦x⟧).out : Quotient s.setoid)
          = (⟦y⟧ : Quotient s.setoid) := by
      exact (h_eq₁.mpr hout)
    have : (Quotient.mk'' (s.fq ⟦x⟧).out : Quotient s.setoid)
            = s.fq ⟦x⟧ :=
    by
      subst hout
      simp_all only [Quotient.out_eq]
    simpa [this] using hout_q

--Lesma regarding when the magnitude of the equivalence class is 1.
private lemma equal_one_setroid (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) (x y: s.V) :
  s.setoid x y ↔ x = y :=
by
  let eo := equal_one s hq1 x y
  constructor
  · intro h
    have : s.setoid x y := by
      exact h
    have : x = y := by
      rw [←Quotient.eq] at this
      exact (equal_one s hq1 x y).mp this
    exact this
  · intro h
    subst h
    exact (@Quotient.eq _ s.setoid x x).mp rfl

--Lesma regarding when the magnitude of the equivalence class is 1.
private lemma po_ideal_system_from_allone_lem (α : Type) [Fintype α] [DecidableEq α] (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) (x y : s.V)(n:Nat):
 s.fq^[n] (@Quotient.mk s.V s.setoid x) = (@Quotient.mk s.V s.setoid y) ↔ (fun x => (s.fq ⟦x⟧).out)^[n] x = y:=
by
  let g : s.V → s.V := fun xx => (s.fq ⟦xx⟧).out
  induction n generalizing x y with
  | zero =>
      simp [Function.iterate_zero, g]
      have h := equal_one_f s hq1 x x
      simp [g] at h
      exact equal_one_setroid s hq1 x y
  | succ k ih =>
      show
        s.fq^[k.succ] ⟦x⟧ = ⟦y⟧
          ↔ (g^[k.succ]) x = y
      rw [Function.iterate_succ']
      rw [Function.iterate_succ']
      set zq  := s.fq^[k] ⟦x⟧ with hzq
      set z   := (g^[k]) x     with hz

      have ih' := (ih x z).trans (by
        simp_all only [Subtype.coe_eta, true_iff, g, zq, z]
        assumption
        )

      have step :=
        (equal_one_f s hq1 (x := z) (y := y)).symm

      constructor
      · intro h
        have : zq = @Quotient.mk _ s.setoid z := by
          simp_all only [Subtype.forall, Subtype.coe_eta, Function.comp_apply, zq, g, z]
        simp
        simp at h
        rw [←hz]
        dsimp [g]
        rw [←hzq] at h
        rw [this] at h
        exact (equal_one_f s hq1 z y).mp h
      · intro h
        have : g^[k] x = z := by
          simp [g, hz]

        have : s.fq ⟦z⟧ = ⟦y⟧ := by
          apply step.mp
          simp
          subst h
          simp_all only [Subtype.forall, Subtype.coe_eta, Function.comp_apply, Quotient.out_eq, zq, g, z]

        have : (Quotient.mk'' (s.fq ⟦z⟧).out : Quotient s.setoid) = ⟦y⟧ := by
          simp_all only [Quotient.out_eq, true_iff]
        have : (s.fq ⟦z⟧).out = y := by
          simp_all only [Quotient.out_eq, true_iff]

        let eos := equal_one_setroid s hq1 z y
        let eof := (equal_one_f s hq1 z y).mpr
        rename_i this_2 this_3
        rw [←this_2]
        have : zq = @Quotient.mk _ s.setoid z := by
          subst h
          simp_all only [Subtype.coe_eta, Quotient.out_eq, zq, z, g]
        exact congrArg s.fq this

--Define the corresponding Setup_po when all equivalence classes are 1.I mainly use it.
noncomputable def po_ideal_system_from_allone {α : Type} [Fintype α] [DecidableEq α] (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1): Setup_po α :=
{
  V := s.V,
  nonemp := by
    exact s.nonemp,
  f := fun x => Quotient.out (s.fq (@Quotient.mk _ s.setoid x)),
  po := po_ideal_system_from_allone_le s hq1,
  order := by
    intro x y
    dsimp [po_ideal_system_from_allone_le]
    constructor
    · intro hxy
      have :s.spo.le (@Quotient.mk s.V s.setoid x) (s.fq (@Quotient.mk s.V s.setoid x)) := by
        apply reach_leq s (@Quotient.mk s.V s.setoid x) (s.fq (@Quotient.mk s.V s.setoid x))
        dsimp [reach]
        use 1
        simp

      have goal: s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) := by
        apply reach_leq s (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y)
        -- Add the necessary proof here
        dsimp [reach]
        dsimp [reach] at hxy
        obtain ⟨n,hnl⟩ := hxy
        use n
        exact (po_ideal_system_from_allone_lem α s hq1 x y n).mpr hnl
      exact goal

    · intro hxy
      let rlr := reach_leq_rev s (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y)
      specialize rlr hxy
      show reach (fun x => (s.fq ⟦x⟧).out) x y
      dsimp [reach]
      dsimp [reach] at rlr
      obtain ⟨n,hnl⟩ := rlr
      use n
      let pisf := po_ideal_system_from_allone_lem α s hq1 x y n
      exact (po_ideal_system_from_allone_lem α s hq1 x y n).mp hnl
}


--What I want to show is that when the nds of the po's ideal are always unpositive, the nds of the Setup_spo2's ideal are always unpositive, but from the above, it is obvious.
lemma po_ideal_system_eq (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) :
  po_closuresystem (po_ideal_system_from_allone s hq1) = spo_closuresystem s:=
by
  dsimp [po_closuresystem, po_ideal_system_from_allone]
  dsimp [spo_closuresystem]
  simp
  ext ss
  constructor
  · intro h
    obtain ⟨hss, h⟩ := h
    use QuotientOf s (ss.subtype (fun x => x ∈ s.V))
    constructor
    · intro q hq q' hq'
      show q' ∈ QuotientOf s (Finset.subtype (fun x => x ∈ s.V) ss)
      let x:= q.out
      let x':= q'.out
      specialize h x x.property
      have : x.val ∈ ss :=
      by
        dsimp [QuotientOf] at hq
        rw [Finset.mem_image] at hq
        simp at hq
        obtain ⟨a,ha1,ha2⟩ := hq
        obtain ⟨ha2,ha3⟩ := ha2
        have : ⟨a,ha2⟩ = x :=
        by
          let eo := equal_one s hq1 ⟨a,ha2⟩ x
          apply eo.mp
          subst ha3
          simp_all only [Subtype.coe_eta, Quotient.out_eq, x]
        simp_all only [Subtype.coe_eta, Quotient.out_eq, coe_mem, le_refl, x]
        obtain ⟨val, property⟩ := x
        obtain ⟨val_1, property_1⟩ := x'
        rwa [← this]
      specialize h this
      specialize h x' x'.property
      have : (po_ideal_system_from_allone s hq1).po.le x' x :=
      by
        rw [←(po_ideal_system_from_allone s hq1).order]
        dsimp [reach]
        rw [s.h_spo] at hq'
        dsimp [partialOrderOfFq] at hq'
        dsimp [reach] at hq'
        obtain ⟨n,hq'⟩ := hq'
        use n
        let pisfa := po_ideal_system_from_allone_lem α s hq1 x' x n
        have :s.fq^[n] ⟦x'⟧ = ⟦x⟧ :=
        by
          subst hq'
          simp_all only [Subtype.coe_eta, Quotient.out_eq, x, x']
        let pis := pisfa.mp this
        exact pis
      specialize h this
      dsimp [QuotientOf]
      rw [Finset.image]
      simp
      use x'
      constructor
      · simp_all only [x, x']
      · simp_all only [Subtype.coe_eta, Quotient.out_eq, coe_mem, exists_const, x, x']

    · constructor
      · simp_all only
      · intro hhs
        constructor
        · intro x hx
          dsimp [QuotientOf]
          rw [Finset.image]
          simp
          use x
          use hx
          have :x ∈ s.V :=
          by
            simp_all only
            exact hhs hx
          use this
        · intro q hq
          intro x hx hh
          have xeqq: x = q.out :=
          by
            symm
            let eo := equal_one2 s hq1 ⟨x,hx⟩
            subst hh
            simp_all only [eo]
          dsimp [QuotientOf] at hq
          rw [Finset.mem_image] at hq
          simp at hq
          obtain ⟨a,ha,ha2⟩ := hq
          obtain ⟨ha2,ha3⟩ := ha2
          have : x = a :=
          by
            have :@Quotient.mk _ s.setoid ⟨x,hx⟩ = @Quotient.mk _ s.setoid ⟨a,ha2⟩ :=
            by
              subst ha3 xeqq
              simp_all only [Subtype.coe_eta, Quotient.out_eq]
            let eo := equal_one s hq1 ⟨x,hx⟩ ⟨a,ha2⟩
            subst ha3 xeqq
            simp_all only [Subtype.coe_eta, Quotient.out_eq]
            cases eo
            simp_all only [Subtype.coe_eta, Quotient.out_eq, forall_const, imp_self]
          rw [this]
          exact ha
  · intro h
    obtain ⟨q, hq⟩ := h
    obtain ⟨hq1, hq2, hq3⟩ := hq
    constructor
    · simp_all only [forall_true_left]
    · intro x1 hx1 hx2 x2 hx21 hx22
      simp_all only [forall_true_left]
      obtain ⟨left, right⟩ := hq3
      apply right
      · apply hq1
        on_goal 2 => {exact hx22
        }
        · simp_all only
      · rfl
