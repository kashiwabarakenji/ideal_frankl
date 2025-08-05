import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
--import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.functionalPartial

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]



open Function Finset

--The parts related to the maximum element of Setup_po have been made independent as functionalPartialMaximal.

def po_maximal (s: Setup_po α) (x: s.V) : Prop := ∀ y, s.po.le x y → x = y

--To be the maximum means that s.f is itself.
--It is also referred to from outside.
lemma po_maximal_lem (s: Setup_po α) (x: s.V) :
  po_maximal s x ↔ s.f x = x :=
by
  constructor
  · intro h
    have h1 : s.po.le x (s.f x) := by
      apply (s.order x (s.f x)).1
      use 1
      simp_all only [Function.iterate_one]
    have h2 : x = s.f x := by
      apply h
      exact h1
    exact id (Eq.symm h2)
  · intro hfx
    dsimp [po_maximal]
    intro y hxy
    -- `≤`  ⇒  `reach`
    have hreach : reach s.f x y := (s.order x y).2 hxy
    rcases hreach with ⟨n, hn⟩
    -- show every iterate of `f` fixes `x`
    have h_iter : s.f^[n] x = x := by
      induction n with
      | zero       => simp
      | succ n ih  =>
          exact Function.iterate_fixed hfx (n + 1)
    -- rewrite the equality obtained from `reach`
    simpa [h_iter] using hn

/--
Repeating `f : α → α` on `Fintype` will result in
Two iterations of `0,1,...,Fintype.card α` match.
-/
private lemma exists_eq_iterate {α : Type u} [DecidableEq α] [Fintype α]
  (f : α → α) (a : α) :
  ∃ m n : ℕ, m < n ∧ f^[m] a = f^[n] a := by
  classical
  -- Put `N = |α|`
  set N : ℕ := Fintype.card α with hN
  -- Consider g : Fin (N+1) → α,  k ↦ f^[k] a
  let g : Fin (N + 1) → α := fun k => (f^[k]) a


  have h_not_inj : ¬Injective g := by
    intro hg

    have h_card := Fintype.card_le_of_injective g hg
    -- |Fin (N+1)| = N+1
    have : N + 1 ≤ N := by
      simp [hN, Fintype.card_fin]
      simp_all only [Fintype.card_fin, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, N, g]
    exact (Nat.not_succ_le_self N) this

  have h_exists_pair :
      ∃ i j : Fin (N + 1), i ≠ j ∧ g i = g j := by
    -- `not_injective_iff` : ¬Inj f ↔ ∃ x y, f x = f y ∧ x ≠ y
    simp [Function.not_injective_iff]
    dsimp [Injective] at h_not_inj
    push_neg at h_not_inj
    obtain ⟨i, j, hEq⟩ := h_not_inj
    use i, j
    rw [and_comm]
    exact hEq

  rcases h_exists_pair with ⟨i, j, hne, hEq⟩
  cases lt_or_gt_of_ne hne with
  | inl hij =>
      exact ⟨i, j, hij, by
        simpa [g] using hEq⟩
  | inr hji =>
      -- swap  i j
      exact ⟨j, i, hji, by
        simp [g, hEq]
        ⟩

--There's always a maximum element above.There is also a reference from outside.
lemma po_maximal_reachable (s : Setup_po α) (y : s.V):
 ∃ x, po_maximal s x ∧ reach s.f y x :=
by

  obtain ⟨m,n,hmn,heq⟩ :=
    exists_eq_iterate (s.f) y   -- m < n かつ f^[m] y = f^[n] y
  set g : ℕ → s.V := fun k => (s.f^[k]) y with hg

  have h_step :
      s.po.le (g m) (g (m+1)) := by

    have : reach s.f (g m) (g (m+1)) := by
      refine ⟨1,?_⟩
      simp [hg, iterate_one, iterate_succ_apply']  -- f^[m+1] = f^[1] (f^[m])
    simpa [hg] using (s.order _ _).1 this

  have h_chain :
      s.po.le (g (m+1)) (g n) := by

    have : reach s.f (g (m+1)) (g n) := by
      refine ⟨n - (m+1), ?_⟩
      -- iterate_add to split the exponent
      have : (s.f^[n - (m+1)]) ((s.f^[m+1]) y) = (s.f^[n]) y := by
        simp [iterate_add, hg, add_comm]
        show s.f^[n - (m + 1)] (s.f^[m] (s.f y)) = s.f^[n] y
        have h := Nat.add_sub_cancel' (Nat.succ_le_of_lt hmn)
        rw [←@comp_apply _ _ _ (s.f^[m]) s.f y ]
        rw [←Function.iterate_succ]
        rw [←@comp_apply _ _ _ s.f^[n - (m + 1)] (s.f^[m.succ]) y ]
        rw [←iterate_add]
        simp_all only [iterate_succ, comp_apply, Nat.succ_eq_add_one, g]
        obtain ⟨val, property⟩ := y
        rw [Nat.sub_add_cancel hmn]
      simpa [hg] using this
    let so := (s.order _ _).1 this
    simp
    exact so

  have h_fix : (s.f^[m] y) = (s.f^[m+1] y) := by
    have : s.po.le (g m) (g (m+1)) ∧ s.po.le (g (m+1)) (g m) := by
      have h₁ := h_step
      have h₂ : s.po.le (g (m+1)) (g m) := by
        simp_all only [iterate_succ, comp_apply, g]

      exact And.intro h₁ h₂

    have := s.po.le_antisymm (g m) (g (m+1)) this.1 this.2
    simpa [hg, iterate_succ_apply'] using this

  let x : s.V := ⟨ (s.f^[m] y).val, by
    simp_all only [iterate_succ, comp_apply, le_refl, coe_mem, g]⟩

  have fx_eq : s.f x = x := by
    -- unwrap the subtype / use h_fix
    --apply Subtype.ext
    --show ↑(s.f x) = x.val
    rw [iterate_succ_apply'] at h_fix
    exact id (Eq.symm h_fix)

  have h_max : po_maximal s x := by
    have := (po_maximal_lem s x).mpr fx_eq
    simpa using this

  have h_reach : reach s.f y x := by
    refine ⟨m, ?_⟩
    -- unfold x
    simp_all only [iterate_succ, comp_apply, Subtype.coe_eta, g, x]

  exact ⟨x, h_max, h_reach⟩

--There is only one element that can be maximized.There is also a reference from outside.
lemma po_maximal_reachable_eq (s : Setup_po α) (y : s.V):
 ∀ x1 x2, (po_maximal s x1 ∧ reach s.f y x1 ) →
          (po_maximal s x2 ∧ reach s.f y x2) →
          x1 = x2 :=
by
  intro x₁ x₂ h₁ h₂
  rcases h₁ with ⟨hmax₁, ⟨k₁, hk₁⟩⟩
  rcases h₂ with ⟨hmax₂, ⟨k₂, hk₂⟩⟩

  cases le_or_gt k₁ k₂ with
  | inl hle =>
      have hreach : reach s.f x₁ x₂ := by
        have : (s.f^[k₂ - k₁]) x₁ = x₂ := by
          have : (s.f^[k₁ + (k₂ - k₁)]) y = x₂ := by
            simpa [Nat.add_sub_cancel' hle] using hk₂
          have : (s.f^[k₂ - k₁]) ((s.f^[k₁]) y) = x₂ := by
            rw [←iterate_add_apply]
            have :k₂ - k₁ + k₁ = k₂ := by
              exact Nat.sub_add_cancel hle
            rw [this]
            exact hk₂

          simpa [hk₁] using this
        exact ⟨k₂ - k₁, this⟩
      have hle₁₂ : s.po.le x₁ x₂ := (s.order _ _).1 hreach
      exact (hmax₁ x₂ hle₁₂)
  | inr hgt =>
      have hreach : reach s.f x₂ x₁ := by
        have : (s.f^[k₁ - k₂]) x₂ = x₁ := by
          have : (s.f^[k₂ + (k₁ - k₂)]) y = x₁ := by
            simpa [Nat.add_sub_cancel' (Nat.le_of_lt hgt)] using hk₁
          have : (s.f^[k₁ - k₂]) ((s.f^[k₂]) y) = x₁ := by
            rw [←iterate_add_apply]
            have :k₁ - k₂ + k₂ = k₁ := by
              exact Nat.sub_add_cancel (Nat.le_of_lt hgt)
            rw [this]
            exact hk₁

          simpa [hk₂] using this
        exact ⟨k₁ - k₂, this⟩
      have hle₂₁ : s.po.le x₂ x₁ := (s.order _ _).1 hreach
      exact (hmax₂ x₁ hle₂₁).symm

--a function that gives only one maximum element
noncomputable def proj_max (s: Setup_po α) (v : {x : α // x ∈ s.V}) : {x : α // x ∈ s.V} :=
  Classical.choose (po_maximal_reachable s v)

--Equivalent relationships of equivalence classes where the maximum elements match.It is also an equivalence relationship of connected components.
def projr (s: Setup_po α)(v w : {x : α // x ∈ s.V}) : Prop := proj_max s v = proj_max s w

--Setoid of the equivalence class that matches the maximum element.
instance proj_setoid {α : Type} [Fintype α] [DecidableEq α] (s: Setup_po α) [DecidableRel (projr s)]: Setoid {x : α // x ∈ s.V} where
  r  := projr s
  iseqv :=
    ⟨
      -- refl: ∀ (v : {x : α // x ∈ s.V}), projr s v v
      fun (_ : {x : α // x ∈ s.V}) => rfl,
      -- symm: ∀ (v w : {x : α // x ∈ s.V}), projr s v w → projr s w v
      @fun (v w : {x : α // x ∈ s.V}) (h : projr s v w) => Eq.symm h,
      -- trans: ∀ (v w u : {x : α // x ∈ s.V}), projr s v w → projr s w u → projr s v u
      fun {v : {x : α // x ∈ s.V}} {w : {x : α // x ∈ s.V}} {u : {x : α // x ∈ s.V}}
          (h₁ : projr s v w) (h₂ : projr s w u) => Eq.trans h₁ h₂
    ⟩

--proj_max is proof that it is truly the source of maximum.
-- Also used with functionalMain.
lemma proj_max_maximal (s: Setup_po α) (v : {x : α // x ∈ s.V}) :
  po_maximal s (proj_max s v) := by
  obtain ⟨x, hmax, _⟩ := Classical.choose_spec (po_maximal_reachable s v)
  exact x

--proj_max is proof that you are above you.It can also be used from outside.
lemma reach_maximal (s: Setup_po α) (v : {x : α // x ∈ s.V}) : reach s.f v (proj_max s v) := by
  -- proof for reachability from v to proj_max s v
  dsimp [proj_max]
  --dsimp [po_maximal_reachable]
  obtain ⟨x, n, hx⟩ := Classical.choose_spec (po_maximal_reachable s v)
  dsimp [reach]
  use n

--Setroid components are equal and maximum elements are equal.
lemma proj_max_quotient (s: Setup_po α) (x y : {x : α // x ∈ s.V}) :
  proj_max s x = proj_max s y ↔ Quotient.mk (proj_setoid s) x = Quotient.mk (proj_setoid s) y := by
  apply Iff.intro
  · intro h
    dsimp [proj_max] at h
    simp_all only [Quotient.eq]
    exact h
  · intro h
    dsimp [proj_max]
    --obtain ⟨x, hmax, _⟩ := Classical.choose_spec (po_maximal_reachable s x)
    --obtain ⟨y, hmax, _⟩ := Classical.choose_spec (po_maximal_reachable s y)
    simp_all only [Quotient.eq]
    exact h

--Retrieves the maximum element from the equivalence class.Proj_max_quotient is not used.
noncomputable def proj_max_of_quot
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup_po α) :
  Quotient (proj_setoid s) →
    {x : α // x ∈ s.V} :=
  Quotient.lift
    (fun v : {x : α // x ∈ s.V} => proj_max s v)
    (by
      intro v w h
      simpa using h)

@[simp] lemma proj_max_of_quot_mk
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup_po α) (v : {x : α // x ∈ s.V}) :
  proj_max_of_quot s ⟦v⟧ = proj_max s v := rfl

--That the maximum element proj_max of y is really the maximum element and is above.It's similar to proj_max_maximal.There's a reference then.
lemma proj_max_spec (s : Setup_po α) (y : s.V) :
  po_maximal s (proj_max s y) ∧ reach s.f y (proj_max s y) :=
  Classical.choose_spec (po_maximal_reachable s y)

--If it is at maximum and is well-able, it should be proj_max.See it from functionalDirectProduct.
lemma proj_max_unique (s : Setup_po α) {y x : s.V}
  (h : po_maximal s x ∧ reach s.f y x) :
  proj_max s y = x := by
  have hy := proj_max_spec s y
  exact po_maximal_reachable_eq s y (proj_max s y) x hy h

--If there is a large and small relationship, the corresponding maximum element proj_max is equal.
private lemma proj_max_order (s: Setup_po α) (x y : {x : α // x ∈ s.V})(od:s.po.le x y) :
 proj_max s x = proj_max s y := by

  dsimp [proj_max]
  rw [←s.order x y] at od
  obtain ⟨xm, hmax, hx⟩ := Classical.choose_spec (po_maximal_reachable s x)
  obtain ⟨ym, hmax, hy⟩ := Classical.choose_spec (po_maximal_reachable s y)
  have : reach s.f y (proj_max s y) := by
    exact reach_maximal s y
  have :reach s.f x (proj_max s y) := by
    --reachのtransitivityの定理があるはず。
    exact reach_trans s.f od this
  apply proj_max_unique s
  constructor
  · simp_all only
  · exact this

--If there is a large and small relationship, the corresponding components are equal.There is an external reference.
lemma quotient_order (s: Setup_po α) (x y : {x : α // x ∈ s.V}) (od:s.po.le x y):
  Quotient.mk (proj_setoid s) x = Quotient.mk (proj_setoid s) y := by

  apply (proj_max_quotient s x y).mp
  exact proj_max_order s x y od

--That the maximum element proj_max of y is really the maximum element and is above.It's similar to proj_max_maximal.There's a reference then.
lemma proj_max_eq_of_maximal
    (s : Setup_po α) (x : s.V) (hmax : po_maximal s x) :
    proj_max s x = x := by
  dsimp [proj_max]
  apply proj_max_unique s
  constructor
  · exact hmax
  · dsimp [reach]
    use 0
    simp


/-
`s : Setup_po α` on the partial order `s.po`
Take the principal ideal generated by `x` as a Finset
-/
noncomputable def principalIdeal (s : Setup_po α) (x : s.V) : Finset α :=
  (s.V.attach.filter (fun y ↦ s.po.le y x)).image Subtype.val

/------------------------------------------------------------
  2. principalIdeal is injective
------------------------------------------------------------/
lemma principal_injective
    (s : Setup_po α) :
    Function.Injective (principalIdeal s) := by
  intro x y hEq
  -- x ≤ y:  x ∈ principalIdeal x  →  filter condition gives x ≤ x (trivial)
  have hx_in : (x : α) ∈ principalIdeal s x := by
    simp [principalIdeal, s.po.le_refl]
  have hx_in_y : (x : α) ∈ principalIdeal s y := by
    simpa [hEq] using hx_in
  have x_le_y : s.po.le x y := by
    -- from filter predicate
    simp [principalIdeal] at hx_in_y
    exact hx_in_y

  have hy_in : (y : α) ∈ principalIdeal s y := by
    simp [principalIdeal, s.po.le_refl]
  have hy_in_x : (y : α) ∈ principalIdeal s x := by
    simpa [hEq] using hy_in
  have y_le_x : s.po.le y x := by
    simp [principalIdeal] at hy_in_x
    exact hy_in_x

  exact s.po.le_antisymm x y x_le_y y_le_x


/------------------------------------------------------------
  3. Image of the map ⊆ ideal set & card calculation
------------------------------------------------------------/
--ideal predicate
def isIdeal (s : Setup_po α) (I : Finset α) : Prop :=
  I ⊆ s.V ∧ ∀ {v w : s.V}, v.1 ∈ I → s.po.le w v → w.1 ∈ I

--I changed SS because I thought it would be easier to use RW if it was used in Forall.
lemma isIdeal_lem (s: Setup_po α) :--(ss : Finset α)(hss : ss ⊆ s.V) :
  ∀ ss : Finset s.V, isIdeal s (ss.image Subtype.val) ↔ ∀ (v : s.V ), v ∈ ss → ∀ w :s.V, s.po.le  w v → w ∈ ss :=
by
  intro ss
  constructor
  · intro h v hv w hle
    have : v ∈ ss := by
      simp_all only
    dsimp [isIdeal] at h
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, coe_mem,
      exists_const, Subtype.forall]
    tauto

  · intro h
    constructor
    ·
      simp_all only [Subtype.forall]
      intro x hx
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      obtain ⟨w, h_1⟩ := hx
      simp_all only
    · intro v w hv hle
      simp_all only [Subtype.forall, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
        Subtype.coe_eta, coe_mem, exists_const]
      obtain ⟨val, property⟩ := v
      obtain ⟨val_1, property_1⟩ := w
      apply h
      on_goal 2 => {exact hle
      }
      · simp_all only

lemma isIdeal_lem2 (s: Setup_po α) :--(ss : Finset α)(hss : ss ⊆ s.V) :
  ∀ ss : Finset α, ss ⊆ s.V → (isIdeal s ss ↔ (po_closuresystem s).sets ss) :=
by
  intro ss hss
  constructor
  · intro h
    have : ∀ v : s.V, v.1 ∈ ss → ∀ w : s.V, s.po.le w v → w.1 ∈ ss := by
      intro v hv w hle
      dsimp [isIdeal] at h
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, coe_mem,
        exists_const, Subtype.forall]
      tauto

    constructor
    · exact hss

    · exact this

  · intro h
    constructor
    · exact h.1

    · intro v w hv hle
      dsimp [po_closuresystem] at h
      simp_all only [Subtype.forall]
      obtain ⟨val, property⟩ := v
      obtain ⟨val_1, property_1⟩ := w
      obtain ⟨left, right⟩ := h
      simp_all only
      apply right
      · exact hv
      · assumption

lemma principal_isIdeal (s : Setup_po α) (x : s.V) :
    isIdeal s (principalIdeal s x) := by
  constructor
  · intro y hy
    simp [principalIdeal] at hy
    obtain ⟨val, property⟩ := x
    obtain ⟨w, h⟩ := hy
    simp_all only

  · intro v w hv hle
    dsimp [principalIdeal] at hv
    dsimp [principalIdeal]
    simp_all only [Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists, exists_and_right,
      exists_eq_right, Subtype.coe_eta, coe_mem, exists_const]
    cases s
    simp_all only
    exact hle.trans hv


--  4. Number of nodes ≤ Ideal

lemma nodes_le_ideals
    (s : Setup_po α) :
    s.V.card + 1 ≤
      (s.V.powerset.filter (isIdeal s)).card := by
  -- define the injection f : V → Ideals
  let f : s.V → Finset α := principalIdeal s
  have hf_inj : Function.Injective f := principal_injective s
  -- f maps into the filter set
  have hf_im :
      ∀ x : s.V, f x ∈ (s.V.powerset.filter (isIdeal s)) := by
    intro x
    have hsub : f x ⊆ s.V := (principal_isIdeal s x).1
    have hpow : f x ∈ s.V.powerset :=
      Finset.mem_powerset.mpr hsub
    have hideal : isIdeal s (f x) := principal_isIdeal s x
    exact Finset.mem_filter.2 ⟨hpow, hideal⟩
  -- Use Finset.card_le_of_inj_on
  let Ideal' := s.V.powerset.filter (isIdeal s) \ {∅}
  have hf_maps :
    ∀ a ∈ s.V.attach, f a ∈ (s.V.powerset.filter (isIdeal s)) := by
    intro ⟨a, ha⟩ _
    exact hf_im ⟨a, ha⟩
  have hf_maps' :
    ∀ a ∈ s.V.attach, f a ∈ Ideal' := by
    intro ⟨a, ha⟩ _
    dsimp [Ideal']
    rw [@mem_sdiff]
    constructor
    · exact hf_im ⟨a, ha⟩
    · simp
      have : a ∈ f ⟨a, ha⟩ := by
        dsimp [f]
        dsimp [principalIdeal]
        rw [Finset.mem_image]
        simp
        exact ha
      rename_i a_1
      simp_all [f, Ideal']
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      simp_all only [Finset.notMem_empty, f, Ideal']
  have hf_inj : InjOn f s.V.attach := by
    intro a b hae hbe h
    apply Subtype.ext
    exact congrArg Subtype.val (hf_inj h)

  let fcl := @Finset.card_le_card_of_injOn s.V (Finset α) s.V.attach _ f hf_maps hf_inj
  simp_all only [mem_filter, Finset.mem_powerset, Subtype.forall, ge_iff_le, f]
  have cardneq: #s.V.attach ≤ #Ideal' := by
      apply Finset.card_le_card_of_injOn
      · exact fun a a_1 => hf_maps' (↑a) a.property a_1
      ·
        rename_i hf_inj_1
        exact hf_inj_1
  have sveq: #s.V = #s.V.attach := by
    exact Eq.symm card_attach

  have :filter (isIdeal s) s.V.powerset = Ideal' ∪ {∅} := by
    apply Finset.ext
    intro ss
    constructor
    · intro h
      simp_all only [Finset.mem_filter, Finset.mem_powerset, Subtype.forall, ge_iff_le, f]
      dsimp [Ideal']
      simp_all only [mem_attach, mem_sdiff, mem_filter, Finset.mem_powerset, and_self, Finset.mem_singleton, true_and,
        forall_const, sdiff_union_self_eq_union, Finset.mem_union, true_or, Ideal', f]
    · intro h
      simp_all only [Finset.mem_filter, Finset.mem_powerset, Subtype.forall, ge_iff_le, f]
      constructor
      · dsimp [Ideal'] at h
        rw [Finset.mem_union] at h
        cases h
        case inl h_1 =>
          simp_all only [mem_attach, mem_sdiff, mem_filter, Finset.mem_powerset, and_self, Finset.mem_singleton, true_and,
            forall_const, sdiff_union_self_eq_union, Finset.mem_union, true_or, Ideal', f]
        case inr h_1 =>
          simp at h_1
          rw [h_1]
          exact Finset.empty_subset s.V
      · dsimp [Ideal'] at h
        rw [Finset.mem_union] at h
        cases h
        case inl h_1 =>
          simp_all only [mem_attach, mem_sdiff, mem_filter, Finset.mem_powerset, and_self, Finset.mem_singleton, true_and,
            forall_const, sdiff_union_self_eq_union, Finset.mem_union, true_or, Ideal', f]
        case inr h_1 =>
          simp at h_1
          rw [h_1]
          dsimp [isIdeal]
          constructor
          · exact Finset.empty_subset s.V
          ·
            intro v w a a_1
            simp_all only [mem_attach, mem_sdiff, mem_filter, Finset.mem_powerset, and_self, Finset.mem_singleton, true_and,
              forall_const, Finset.notMem_empty, f, Ideal']

  have : #Ideal' + 1 = #(filter (isIdeal s) s.V.powerset) := by
    rw [this]
    show #Ideal' + 1 = #(Ideal' ∪ {∅})
    have :   Ideal' ∩ {∅} = ∅ := by
      dsimp [Ideal']
      exact sdiff_inter_self {∅} (filter (isIdeal s) s.V.powerset)
    have : Disjoint {∅} Ideal' := by
      exact Disjoint.symm sdiff_disjoint
    let fcu := Finset.card_union_of_disjoint this
    rw [union_comm {∅} Ideal'] at fcu
    rw [fcu]
    exact Nat.add_comm (#Ideal') 1

  rw [←this]
  rw [sveq]
  exact Nat.add_le_add_right cardneq 1
