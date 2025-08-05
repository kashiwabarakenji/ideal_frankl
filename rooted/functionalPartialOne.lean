import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
--import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.DirectProduct
import rooted.functionalPartialMaximal
import rooted.functionalPartialTrace
import rooted.functionalDirectProduct

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

--I want to prove that when there are one connected component, the maximum element becomes the maximum element and the order is 1.
--I want to show that nds does not increase even if I trace that element.


--If there is one connected component, there is one element of the equivalent value.I'm using it below.
private lemma quotient_subsingleton
    (s : Setup_po α)
    (h : numClasses (proj_setoid s) = 1) :
    Subsingleton (Quotient (proj_setoid s)) := by

  dsimp [numClasses] at h


  obtain ⟨q0, hmem⟩ := Finset.card_eq_one.1 h

  have hmem' : Finset.univ.image (Quot.mk (proj_setoid s)) = {q0} :=
  by
    simp_all only [Finset.card_singleton, univ_eq_attach]
    convert hmem
  refine ⟨?eq⟩
  intro q1 q2
  have hq1 : q1 = q0 := by
    have : q1 ∈ (Finset.univ.image (Quot.mk _)) := by

      rcases Quot.exists_rep q1 with ⟨v, rfl⟩
      simp
    rw [hmem'] at this
    exact Finset.mem_singleton.1 this

  have hq2 : q2 = q0 := by
    have : q2 ∈ (Finset.univ.image (Quot.mk _)) := by
      rcases Quot.exists_rep q2 with ⟨v, rfl⟩
      rw [hmem']
      simp
      have hv : v ∈ s.V.attach := by exact mem_attach s.V v

      have : Quot.mk (proj_setoid s) v ∈ Finset.image (Quot.mk (proj_setoid s)) s.V.attach :=
        Finset.mem_image_of_mem (Quot.mk (proj_setoid s)) hv

      have : Quot.mk (⇑(proj_setoid s)) v ∈ ({q0}:Finset (Quotient (proj_setoid s))) :=
      by
        convert this
        exact id (Eq.symm hmem')
      exact Finset.mem_singleton.1 this

    apply Finset.mem_singleton.1
    rw [hmem'] at this
    exact this

  simp [hq1, hq2]


--If there is one connected component, the maximum element is equal.I'm using it below.
private lemma proj_max_eq_of_one_class
    (s : Setup_po α) (h : numClasses (proj_setoid s) = 1)
    (x y : {x : α // x ∈ s.V}) :
    proj_max s y = proj_max s x := by
  haveI : Subsingleton (Quotient (proj_setoid s)) :=
    quotient_subsingleton s h
  have hquot :
      (Quotient.mk (proj_setoid s) x :
        Quotient (proj_setoid s)) =
      Quotient.mk (proj_setoid s) y := Subsingleton.elim _ _
  exact (proj_max_quotient s y x).mpr (id (Eq.symm hquot))


--I'm also using it from outside.If the number of components is 1, the hyperedge containing the maximum elements becomes the whole set.
theorem component_one
    (s : Setup_po α)
    (h1 : numClasses (proj_setoid s) = 1) :
    ∀ ss : Finset α, ∀ x : s.V,
      (po_closuresystem s).sets ss →
      x.val ∈ ss →
      po_maximal s x →
      ss = s.V := by
  intro ss x hset hx hmax
  have hsubset : ss ⊆ s.V := hset.1
  have hsuperset : s.V ⊆ ss := by
    intro a haV
    let y : s.V := ⟨a, haV⟩
    have hproj : proj_max s y = x := by
      have := proj_max_eq_of_one_class s h1 x y
      have hxproj : proj_max s x = x :=
        proj_max_eq_of_maximal s x hmax
      simpa [hxproj] using this
    have hle : s.po.le y x := by
      have hreach : reach s.f y (proj_max s y) := by
        obtain ⟨_, _, h⟩ := Classical.choose_spec
                                (po_maximal_reachable s y)
        exact reach_maximal s y
      have : reach s.f y x := by
        simpa [hproj] using hreach
      exact (s.order y x).1 this
    have hdown := hset.2 x hx y hle
    simpa using hdown

  exact Finset.Subset.antisymm hsubset hsuperset

------------------------------------------------------------
--- for normalized_degree_sum_gt
------------------------------------------------------------

private lemma po_trace_le_iff
    (s : Setup_po α) (x : s.V) (mx : po_maximal s x)
    (nontriv : s.V.card ≥ 2)
    {a b : s.V}
    (ha : (a : α) ≠ x) (hb : (b : α) ≠ x) :
  let a' : (po_trace s x mx nontriv).V :=
        ⟨a, by
          exact Finset.mem_erase.mpr ⟨ha, a.property⟩⟩
  let b' : (po_trace s x mx nontriv).V :=
        ⟨b, by
          exact Finset.mem_erase.mpr ⟨hb, b.property⟩⟩
  (po_trace s x mx nontriv).po.le a' b'
    ↔ s.po.le a b := by

  simp
    [ po_trace
    , Finset.mem_erase, ha, hb
    ]


private lemma not_mem_of_subset_erase
  {α : Type _} [DecidableEq α]
  {x : α} {ss ground : Finset α}
  (h : ss ⊆ ground.erase x) :
  x ∉ ss := by
  intro hx
  have : x ∈ ground.erase x := h hx
  exact (Finset.mem_erase.1 this).1 rfl

-- The idea after a trace is the original idea, excluding the overall set.I'm using it below.
-- The connected component holds under the assumption of 1.
private lemma trace_sets_iff (s  : Setup_po α) (conn  : numClasses (proj_setoid s) = 1)  (x  : s.V) (mx : po_maximal s x) (nontriv : s.V.card ≥ 2)(ss : Finset α) :
    (po_closuresystem (po_trace s x mx nontriv)).sets ss
    ↔ (po_closuresystem s).sets ss ∧ ss ≠ s.V :=
by
  let t := po_trace s x mx nontriv
  have tV : t.V = s.V.erase x := by
    simp [t, po_trace]

  have forward :
      (po_closuresystem t).sets ss →
        (po_closuresystem s).sets ss ∧ ss ≠ s.V := by
    intro h_t

    have h_sub_erase : ss ⊆ s.V.erase x := by
      have : ss ⊆ t.V := (po_closuresystem t).inc_ground ss h_t
      simpa [tV] using this
    have h_sub_V : ss ⊆ s.V := by
      exact subset_trans h_sub_erase (Finset.erase_subset _ _)

    have hx_not : (x : α) ∉ ss :=
    by
      let nms :=  not_mem_of_subset_erase h_sub_erase
      exact nms
    have h_ne : ss ≠ s.V := by
      intro h_eq
      have : (x : α) ∈ ss := by
        have : (x : α) ∈ s.V := x.property
        simp [h_eq]
      exact hx_not this

    have h_down : ∀ v : s.V, v.1 ∈ ss →
        ∀ w : s.V, s.po.le w v → w.1 ∈ ss := by
      intro v hv w hw
      by_cases hvx : (v : α) = x
      · exfalso
        have : (x : α) ∈ ss := by simpa [hvx] using hv
        exact hx_not this
      have hv_in : (v : α) ∈ s.V.erase x :=
        h_sub_erase hv
      have w_case : (w : α) ≠ x := by
        by_contra hwx
        have hle : s.po.le x v := by
          simp_all only [ne_eq, mem_erase, not_false_eq_true, coe_mem, and_self, t]
          obtain ⟨val, property⟩ := x
          obtain ⟨val_1, property_1⟩ := v
          obtain ⟨val_2, property_2⟩ := w
          subst hwx
          simp_all only

        have h_eq : (x : s.V) = v := mx v hle
        have : (v : α) = x :=
        by
          apply congrArg Subtype.val
          exact id (Eq.symm h_eq)
        exact hvx this
      have hw_in : (w : α) ∈ s.V.erase x := by
        exact Finset.mem_erase.mpr ⟨w_case, w.property⟩

      let v'  : t.V := ⟨v, hv_in⟩
      let w'  : t.V := ⟨w, hw_in⟩

      have h_le' : t.po.le w' v' := by
        have := (po_trace_le_iff s x mx nontriv
                    (a:=⟨w, w.property⟩) (b:=⟨v, v.property⟩)
                    w_case hvx).mpr hw
        simpa [w', v'] using this

      have : w.1 ∈ ss := by
        have hv' : v'.1 ∈ ss := by
          dsimp [v'] at *
          simpa using hv
        have := h_t.2 v' hv' w' h_le'
        simpa [w'] using this
      exact this

    exact And.intro (And.intro h_sub_V h_down) h_ne

  have backward :
      (po_closuresystem s).sets ss ∧ ss ≠ s.V →
        (po_closuresystem t).sets ss := by
    rintro ⟨h_s, h_ne⟩

    have hx_not : (x : α) ∉ ss := by
      by_contra hx
      have h_eq := component_one s conn ss x h_s hx mx
      exact h_ne h_eq

    have h_sub_erase : ss ⊆ s.V.erase x := by
      intro a ha
      have haV : a ∈ s.V := (h_s.1 ha)
      by_cases hax : a = x
      · exfalso
        have : (x : α) ∈ ss := by simpa [hax] using ha
        exact hx_not this
      · exact Finset.mem_erase.mpr ⟨hax, haV⟩

    have h_down_t :
        ∀ v' : t.V, v'.1 ∈ ss →
          ∀ w' : t.V, t.po.le w' v' → w'.1 ∈ ss := by
      intro v' hv w' hw

      let v : s.V :=
        ⟨v', (Finset.mem_of_mem_erase v'.property)⟩
      let w : s.V :=
        ⟨w', (Finset.mem_of_mem_erase w'.property)⟩
      have hv_s : v.1 ∈ ss := by
        dsimp [v] at *
        simpa using hv

      have h_le : s.po.le w v := by
        have := (po_trace_le_iff s x mx nontriv
                    (a:=w) (b:=v)
                    (by
                      intro h; exact (Finset.mem_erase.1 w'.property).1 h)
                    (by
                      intro h; exact (Finset.mem_erase.1 v'.property).1 h)).1 hw
        simpa using this

      have := h_s.2 v hv_s w h_le
      simpa [w] using this


    exact And.intro h_sub_erase h_down_t

  exact ⟨forward, backward⟩

section numberof

variable {α : Type _} [Fintype α] [DecidableEq α]

variable (s : Setup_po α)
variable (x  : s.V) (mx : po_maximal s x)
variable (conn : numClasses (proj_setoid s) = 1)
variable (nontriv : s.V.card ≥ 2)

noncomputable
def ideals (F : SetFamily α) [DecidablePred F.sets] : Finset (Finset α) :=
  F.ground.powerset.filter F.sets


abbrev Fₛ  : ClosureSystem α := po_closuresystem s
abbrev t   : Setup_po α      := (po_trace s x mx nontriv)
abbrev Fₜ  : ClosureSystem α := po_closuresystem (po_trace s x mx nontriv)

noncomputable
instance : DecidablePred (Fₛ s).sets := Classical.decPred _
noncomputable
instance : DecidablePred (Fₜ s x mx nontriv).sets := Classical.decPred _


private lemma ideals_eq_erase (s : Setup_po α) (conn  : numClasses (proj_setoid s) = 1)(x  : s.V) (mx : po_maximal s x) (nontriv : s.V.card ≥ 2):
    (ideals (po_closuresystem (po_trace s x mx nontriv)).toSetFamily) =
      (ideals (po_closuresystem s).toSetFamily).erase (s.V) := by
  dsimp [ideals]

  have tV : (po_trace s x mx nontriv).V = s.V.erase x := by
    simp [po_trace]

  set Iₛ : Finset (Finset α) :=
      (s.V.powerset).filter (po_closuresystem s).sets with hIₛ
  set Iₜ : Finset (Finset α) :=
      ((s.V.erase x).powerset).filter
        (po_closuresystem (po_trace s x mx nontriv)).sets with hIₜ

  have sub :
      Iₜ ⊆ Iₛ.erase (s.V) := by
    intro ss hss
    have h_memₜ :
        ss ∈ (s.V.erase x).powerset ∧
        (Fₜ s x mx nontriv).sets ss := by
      simpa [hIₜ] using (Finset.mem_filter.1 hss)
    have h_setsₜ := h_memₜ.2
    have h_sub : ss ⊆ s.V.erase x :=
      (Finset.mem_powerset.1 h_memₜ.1)

    have h_setsₛ_and_ne :
        (Fₛ s).sets ss ∧ ss ≠ s.V := by
      have := (trace_sets_iff s conn x mx nontriv ss).1 h_setsₜ
      exact this

    have h_in_Iₛ : ss ∈ Iₛ := by
      have hp : ss ∈ s.V.powerset := by

        have : ss ⊆ s.V := subset_trans h_sub (Finset.erase_subset _ _)
        exact (Finset.mem_powerset.2 this)
      simp [hIₛ, hp, h_setsₛ_and_ne.1]

    have : ss ≠ s.V := h_setsₛ_and_ne.2
    show ss ∈ Iₛ.erase (s.V)
    · exact Finset.mem_erase.2 ⟨this, h_in_Iₛ⟩

  have sup :
      Iₛ.erase (s.V) ⊆ Iₜ := by
    intro ss hss
    have ⟨hne, hIₛmem⟩ := Finset.mem_erase.1 hss

    have h_setsₛ : (Fₛ s).sets ss := by
      have := (Finset.mem_filter.1 hIₛmem).2
      simpa [Fₛ] using this

    have hx_not : (x : α) ∉ ss := by
      by_contra hx
      have h_eq := component_one s conn ss x h_setsₛ hx mx
      exact hne h_eq

    have h_sub : ss ⊆ s.V.erase x := by
      intro a ha
      have haV : a ∈ s.V :=
      by
        simp_all [Iₛ, Iₜ]
        obtain ⟨val, property⟩ := x
        simp_all only
        exact hIₛmem ha

      by_cases hax : a = x
      · exfalso
        exact hx_not (by simpa [hax] using ha)
      · exact Finset.mem_erase.2 ⟨hax, haV⟩

    have h_setsₜ :
        (Fₜ s x mx nontriv).sets ss := by
      have : (Fₛ s).sets ss ∧ ss ≠ s.V := by
        exact ⟨h_setsₛ, hne⟩
      exact (trace_sets_iff s conn x mx nontriv ss).2 this

    have h_in_powerset : ss ∈ (s.V.erase x).powerset := by
      exact (Finset.mem_powerset.2 h_sub)
    have : ss ∈ Iₜ := by
      simp_all only [ge_iff_le, mem_erase, ne_eq, not_false_eq_true, mem_filter, Finset.mem_powerset, and_true,
        true_and, and_self, Iₜ, Iₛ]
    exact this

  exact Finset.Subset.antisymm sub sup
------------------------------------------------------------------------
private lemma number_of_hyperedges_trace (s : Setup_po α) (conn  : numClasses (proj_setoid s) = 1)(x  : s.V) (mx : po_maximal s x) (nontriv : s.V.card ≥ 2):
 (po_closuresystem s).toSetFamily.number_of_hyperedges =
    (po_closuresystem (po_trace s x mx nontriv)).toSetFamily.number_of_hyperedges +1 :=

by
  dsimp [SetFamily.number_of_hyperedges]

  have h_card :
      ((ideals (po_closuresystem s).toSetFamily).erase (s.V)).card + 1 =
        (ideals (po_closuresystem s).toSetFamily).card := by
    apply Finset.card_erase_add_one

    have h_ground_sets : (Fₛ s).sets s.V :=
      (Fₛ s).has_ground
    have h_mem :
        s.V ∈ (s.V.powerset).filter (Fₛ s).sets := by
      have hp : s.V ∈ s.V.powerset :=
        (Finset.mem_powerset.2 (Finset.Subset.refl _))
      simpa [ideals, Fₛ] using
        (Finset.mem_filter.2 ⟨hp, h_ground_sets⟩)
    simp [ideals, Fₛ]
    simp_all only [ge_iff_le, mem_filter, Finset.mem_powerset, subset_refl, and_self, and_true]
    obtain ⟨val, property⟩ := x
    rfl

  have : Int.ofNat ((ideals (po_closuresystem s).toSetFamily).card)
        = Int.ofNat ((ideals (po_closuresystem s).toSetFamily).erase (s.V)).card + 1 := by
    simpa [Int.natCast_add, Int.ofNat_one] using congrArg Int.ofNat h_card.symm
  let iee := ideals_eq_erase s conn x mx nontriv
  symm
  ring_nf

  have goal₁ : 1 +  Int.ofNat #((ideals (po_closuresystem s).toSetFamily).erase s.V) = Int.ofNat #(ideals (po_closuresystem s).toSetFamily) := by
    rw [add_comm]
    simp_all only [ge_iff_le, Int.ofNat_eq_coe]

  dsimp [ideals] at goal₁
  simp_all only [ge_iff_le, Int.ofNat_eq_coe]
  obtain ⟨val, property⟩ := x
  convert goal₁

--Assuming one connected component.Total_size after trace.I'm using it below.
private lemma total_size_of_hyperedge_trace
  (s : Setup_po α)
  (conn  : numClasses (proj_setoid s) = 1)
  (x : s.V) (mx : po_maximal s x)
  (nontriv : s.V.card ≥ 2) :
  (po_closuresystem s).toSetFamily.total_size_of_hyperedges
    = (po_closuresystem (po_trace s x mx nontriv)).toSetFamily.total_size_of_hyperedges
      + s.V.card := by
  dsimp [SetFamily.total_size_of_hyperedges, ideals]
  let I := ideals (po_closuresystem s).toSetFamily

  have hG : s.V ∈ I := by
    dsimp [ideals]
    have : s.V ∈ s.V.powerset := by
      apply Finset.mem_powerset.mpr
      exact fun ⦃a⦄ a => a
    simp_all only [ge_iff_le, Finset.mem_powerset, subset_refl, I]
    obtain ⟨val, property⟩ := x
    simp only [ideals]
    simp_all only [mem_filter, Finset.mem_powerset]
    apply And.intro
    · rfl
    · simp only [po_closuresystem, conn]
      simp_all only [subset_refl, coe_mem, implies_true, imp_self, and_self]

  -- 3) sum_erase_add で (I.erase s.V).sum + s.V.card = I.sum
  have h_sum : (I.erase s.V).sum Finset.card + s.V.card = I.sum Finset.card :=
  by
    apply Finset.sum_erase_add
    simp_all only [ge_iff_le, I]

  simp [ideals_eq_erase s conn x mx nontriv, Int.natCast_add]
  let cih := congrArg Int.ofNat h_sum.symm
  dsimp [I,ideals] at h_sum cih
  convert cih
  · exact
      Eq.symm
        (Nat.cast_sum
          (filter (po_closuresystem s).sets (po_closuresystem s).ground.powerset)
          card)
  · norm_cast

    let iee := ideals_eq_erase s conn x mx nontriv
    exact congrFun (congrArg Finset.sum iee) fun x => #x


private lemma normalized_degree_sum_trace
  (s : Setup_po α)
  (conn  : numClasses (proj_setoid s) = 1)
  (x : s.V) (mx : po_maximal s x)
  (nontriv : s.V.card ≥ 2) :
  (po_closuresystem s).toSetFamily.normalized_degree_sum
= (po_closuresystem (po_trace s x mx nontriv)).toSetFamily.normalized_degree_sum
  + ((Int.ofNat s.V.card) - (po_closuresystem (po_trace s x mx nontriv)).number_of_hyperedges)
   :=
by

  dsimp [SetFamily.normalized_degree_sum]

  have hG : s.V ∈ ideals (po_closuresystem s).toSetFamily := by
    dsimp [ideals]
    have hp : s.V ∈ s.V.powerset := by
      apply Finset.mem_powerset.mpr
      exact fun ⦃a⦄ a => a
    simp [ideals]
    let fmf := Finset.mem_filter.mpr ⟨hp, (po_closuresystem s).has_ground⟩
    simp_all only [ge_iff_le]
    obtain ⟨val, property⟩ := x
    apply And.intro
    · rfl
    · rw [mem_filter] at fmf
      simp_all only [Finset.mem_powerset, subset_refl, true_and]

  have : #(po_closuresystem (po_trace s x mx nontriv)).ground + 1=
      #(po_closuresystem s).ground := by
    dsimp [po_closuresystem]
    dsimp [po_trace]
    simp_all only [ge_iff_le, coe_mem, card_erase_of_mem]
    obtain ⟨val, property⟩ := x
    omega
  rw [←this]
  norm_cast
  have hground:#(po_closuresystem (po_trace s x mx nontriv)).ground + 1 = s.V.card :=
  by
    simp_all only
    obtain ⟨val, property⟩ := x
    rfl
  rw [←hground]
  ring_nf
  norm_cast

  let tsht := total_size_of_hyperedge_trace s conn x mx nontriv
  let nht := number_of_hyperedges_trace s conn x mx nontriv
  rw [tsht, nht]
  ring_nf

  set pn := (po_closuresystem (po_trace s x mx nontriv)).number_of_hyperedges with hpn
  set pg := ((po_closuresystem (po_trace s x mx nontriv)).ground.card : ℤ) with hpg
  rw [←hground]
  suffices h_sub : (pg + 1) * 2 + (-(pn * (pg + 1)) - (pg + 1)) = (-pn - pn * pg) + (pg + 1) from
  by
    ring_nf
    simp_all only [Nat.cast_add, Nat.cast_one, pn, pg]
    ring_nf

  simp_all only [pn, pg]
  ring

noncomputable
def principalIdealTrace (s : Setup_po α) (x : s.V) (mx) (nontriv)
    (v : (po_trace s x mx nontriv).V) : Finset α :=
  principalIdeal (po_trace s x mx nontriv) v



--It's not one more case of monojectivity, but the empty set is also hyperedge and not principalIdeal, so it holds true.
private lemma normalized_degree_sum_lem
  (s : Setup_po α)
  --(conn  : numClasses (proj_setoid s) = 1)
  (x : s.V) (mx : po_maximal s x)
  (nontriv : s.V.card ≥ 2):
(Int.ofNat s.V.card) ≤ (po_closuresystem (po_trace s x mx nontriv)).number_of_hyperedges :=
by
  have :#(po_trace s x mx nontriv).V + 1 = Int.ofNat #s.V := by
    dsimp [po_trace]
    simp_all only [ge_iff_le, coe_mem, card_erase_of_mem]
    obtain ⟨val, property⟩ := x
    norm_cast
    omega

  rw [←this]

  let nli := nodes_le_ideals (po_trace s x mx nontriv)

  let iil2 :=isIdeal_lem2 (po_trace s x mx nontriv)

  have :(filter (fun s_1 => (po_closuresystem (po_trace s x mx nontriv)).sets s_1)) (po_trace s x mx nontriv).V.powerset =
      (filter (isIdeal (po_trace s x mx nontriv)) (po_trace s x mx nontriv).V.powerset) :=
  by
    simp_all only [Int.ofNat_eq_coe]
    obtain ⟨val, property⟩ := x
    ext a : 1
    simp_all only [mem_filter, Finset.mem_powerset, and_congr_right_iff, implies_true, iil2]

  dsimp [SetFamily.number_of_hyperedges]

  rw [←this] at nli

  exact Int.toNat_le.mp nli

--Used with functionalMain.
--trace does not reduce normalized_Degree_sum.
--It may be possible to move to PartialTrace, but the theorem is based on the assumption that the number of connected components is 1.
theorem normalized_degree_sum_gt
  (s : Setup_po α)
  (conn  : numClasses (proj_setoid s) = 1)
  (x : s.V) (mx : po_maximal s x)
  (nontriv : s.V.card ≥ 2) :
  (po_closuresystem s).toSetFamily.normalized_degree_sum
  ≤ (po_closuresystem (po_trace s x mx nontriv)).toSetFamily.normalized_degree_sum :=
by

  let ndst := normalized_degree_sum_trace s conn x mx nontriv
  rw [ndst]

  let ndsl := normalized_degree_sum_lem s x mx nontriv

  simp_all only [Int.ofNat_eq_coe, add_le_iff_nonpos_right, tsub_le_iff_right, zero_add, ge_iff_le]
  obtain ⟨val, property⟩ := x
  exact ndsl

--Used with functionalMain.
lemma trace_one_ground_card
  (s : Setup_po α)
  (x : s.V) (mx : po_maximal s x)
  (nontriv : s.V.card ≥ 2) :
  (po_closuresystem s).ground.card
  > (po_closuresystem (po_trace s x mx nontriv)).ground.card :=
by
  dsimp [po_closuresystem]
  dsimp [po_trace]
  simp_all only [ge_iff_le, coe_mem, card_erase_of_mem, gt_iff_lt, tsub_lt_self_iff, card_pos, Nat.lt_one_iff,
    pos_of_gt, and_true]
  obtain ⟨val, property⟩ := x
  exact ⟨val, property⟩
