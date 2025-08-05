-- Discussion of paths regarding pre-order.
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
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne
import rooted.functionalCommon

open Finset Set Classical

set_option maxHeartbeats 500000

variable {α : Type} [Fintype α] [DecidableEq α]

--The first half shows the lemma related to Setup.Continuing the contents of Common.
-- indicates that the amount of preorder is equal to that of reaching in a chain of f.
--The second half is a lemma about the previous order set that we are thinking about.
-- The main theorem in this file is that, in the setoid equivalence class caused by a preorder created from function f, if the equivalence class is 2 or more, it becomes a maximum element.

private lemma size_one_preorder_setup_lemma (s: Setup α) (x y : {x : α // x ∈ s.V}) :
  s.pre.le x y ↔  @Relation.ReflTransGen s.V (R_from_RS1 (rootedset_from_setup s))  y x:=
by
  simp [rootedset_from_setup]
  rw [s.h_pre]
  dsimp [size_one_preorder]
  dsimp [size_one_circuits_preorder]
  dsimp [rootedset_onestem_eachvertex_V]
  apply Iff.intro
  · intro h
    apply preorder.R_hat.to_ReflTransGen
    exact h

  · intro h
    intro s1 hs1
    exact preorder.ReflTransGen.to_R_hat h s1 hs1

-- If f has a last-minute relationship, a <= b.I thought it was obvious, but I couldn't prove it unless I followed the definition in depth.
-- Both path_implies_le and size_one_preorder_setup_step are not in the file, see this lemma.
-- You might want to move this to common.
theorem f_and_pre (su: Setup α) (a b : {x // x ∈ su.V}) (sf : su.f a = b ) : su.pre.le a b := by
  rw [su.h_pre]
  dsimp [size_one_preorder]
  dsimp [size_one_circuits_preorder]
  dsimp [preorder.R_hat]
  intro s hs hhs
  dsimp [preorder.S_R] at hs
  rw [Finset.mem_filter] at hs
  dsimp [rootedset_onestem_eachvertex_V] at hs
  simp at hs
  dsimp [preorder.closedUnder] at hs
  let hs2 := hs.2
  dsimp [R_from_RS1] at hs2
  simp at hs2
  specialize hs2 b b.property
  specialize hs2 a a.property
  have : a.val ∉ ({b.val}:Finset α) := by
    intro h
    rw [Finset.mem_singleton] at h
    rw [←sf] at h
    let suv := su.valid a
    have : a = (su.f a) := by
      exact Subtype.eq h
    rw [←this] at suv
    contradiction
  let vp := ValidPair.mk {b.val} a.val this
  specialize hs2 vp
  simp at hs2
  specialize hs2 a
  simp at hs2
  apply hs2
  dsimp [vp]
  ext
  · simp
    rw [sf]
  · simp
  · dsimp [vp]
  · dsimp [vp]
  · exact hhs

-------Here's the part about repeating f------

-- Iteration is based on the setup_spo, but it is written as reach in functionalSPO, and some are used, and some may overlap.
--What you reach with iteration has something to do with size.

-- f_and_pre is used for proof.
-- It may not be referenced from outside.Referenced from iteratef_lemma_two.

private lemma iteratef_lemma (s: Setup α) (x : s.V):
  ∀ n, s.pre.le x (s.f^[n] x) := by
  intro n
  induction n generalizing x
  case zero =>
      simp_all only [Function.iterate_zero, id_eq, le_refl]

  case succ n ih =>
      rw [Function.iterate_succ]
      simp
      have ihh:s.pre.le (s.f x) (s.f^[n] (s.f x)) := by
        simp_all only [Subtype.forall]
      have : s.pre.le (x) (s.f x) := by
        apply f_and_pre
        simp_all only [Subtype.forall]
      exact s.pre.le_trans x (s.f x) (s.f^[n] (s.f x)) this ihh

--Prove iteratef_lemma_ref without using path.
private lemma exists_iterate_eq_of_rtg
    {α : Type} [Fintype α] [DecidableEq α]
    {s : Setup α} {x y : s.V}
    (h : Relation.ReflTransGen (fun a b : s.V ↦ s.f a = b) x y) :
  ∃ n : ℕ, (s.f^[n]) x = y := by
  induction h with
  | refl      => exact ⟨0, rfl⟩
  | tail h₁ h₂ ih =>
      rcases ih with ⟨n, rfl⟩
      exact ⟨n.succ, by
        rename_i c
        rw [←h₂]
        rw [Function.iterate_succ' s.f n]
        exact rfl
      ⟩

-- A lemma regarding the difference in expressions when taking a step before taking a transitive closure.It was set as a set-up premise.
-- There are no references from the file.
private lemma size_one_preorder_setup_step (s: Setup α) (x y : {x : α // x ∈ s.V}) :
  R_from_RS1 (rootedset_from_setup s) y x ↔ s.f x = y :=
by
  dsimp [rootedset_from_setup]
  dsimp [rootedset_onestem_eachvertex_V]
  dsimp [R_from_RS1]
  apply Iff.intro
  · intro h
    simp [rootedset_onestem_eachvertex_V] at h
    obtain ⟨val, property⟩ := h
    obtain ⟨val_1, property_1⟩ := property
    obtain ⟨val_2, property_2⟩ := property_1
    obtain ⟨val_2, property⟩ := x
    obtain ⟨val_3, property_1⟩ := y
    obtain ⟨w, h⟩ := val_1
    obtain ⟨w_1, h⟩ := h
    subst h val_2
    simp_all only [singleton_inj]
    subst property_2
    simp_all only [Subtype.coe_eta]
  · intro h
    have : x.val ∉ ({y.val} :Finset α):=
    by
      rw [←h]
      simp
      by_contra h_contra
      have noteq:  ¬ ↑x = ↑(s.f x) :=
      by
        let sv := s.valid x
        exact id (Ne.symm sv)
      have :(s.f x) = x := by
        apply Subtype.eq
        subst h
        simp_all only
      rw [this] at noteq
      contradiction

    let vp := ValidPair.mk {y.val} x.val this
    use vp
    simp
    constructor
    ·
      subst h
      simp_all only [ValidPair.mk.injEq, singleton_inj, exists_and_right, exists_eq_right, Subtype.coe_eta, coe_mem,
        exists_const, vp]
    ·
      subst h
      simp_all only [and_self, vp]

--- It hasn't been used since then.It's better to quote other things that are easier to use.
--This method may be simpler to define the order from f.
-- Name changed from size_one_preorder_setup_lemma2
private lemma  size_one_preorder_eq_transition (s : Setup α) (x y : s.V):
  s.pre.le x y ↔
  Relation.ReflTransGen (fun a b : s.V ↦ s.f a = b) x y := by
  let sop := size_one_preorder_setup_lemma s x y
  have : (R_from_RS1 (rootedset_from_setup s)) = (fun b a : s.V ↦ s.f a = b):= by
    ext a b
    let sop3 := Iff.symm (size_one_preorder_setup_step s a b)
    exact size_one_preorder_setup_step s b a

  have :Relation.ReflTransGen (R_from_RS1 (rootedset_from_setup s)) y x ↔
    Relation.ReflTransGen (fun a b : s.V ↦ s.f a = b) x y := by
    rw [this]
    exact Relation.reflTransGen_swap

  exact Iff.trans sop this

-- This is the theorem I wanted to prove.If there is a relationship between size and size in preorder, it will be delivered with reach.

theorem iteratef_lemma_ref
    (s : Setup α) (x y : s.V)
    (h : s.pre.le x y) :
  ∃ n : ℕ, (s.f^[n]) x = y := by
  have h' : Relation.ReflTransGen (fun a b : s.V ↦ s.f a = b) x y :=
    (size_one_preorder_eq_transition s x y).1 h
  exact exists_iterate_eq_of_rtg h'

-- The number of iterations and the size of the size.
--The path argument is not used.
private lemma iteratef_lemma_two (s: Setup α) (x: s.V) (n1 n2: Nat) :
  n1 < n2 → s.pre.le (s.f^[n1] x) (s.f^[n2] x) :=
by
  intro h
  let n := n2 - n1
  have : n + n1 = n2 := by
    simp_all only [n]
    obtain ⟨val, property⟩ := x
    omega
  have : s.f^[n] (s.f^[n1] x) = s.f^[n2] x := by
    rw [←this]
    rw [Function.iterate_add]
    exact rfl
  let il := iteratef_lemma s (s.f^[n1] x) n
  rw [this] at il
  exact il

--Lemma: The whole iteration of f is overlapping.
-- Proof: The Pillar's Nest Principle.Fintype.exists_ne_map_eq_of_card_lt is the point.
--The path argument is not used.
private lemma iteratef_pigeon (s: Setup α) (x: s.V)  : ∃ (n1 n2: Nat), n1 ≠ n2 ∧ (s.f^[n1] x) = s.f^[n2] x :=
by
  let dom := (Finset.Icc 0 (s.V.card + 1)).image (fun i => (s.f^[i] x))
  have : s.V.card < ((Finset.Icc 0 (s.V.card + 1))).card := by
    simp_all only [Nat.card_Icc, tsub_zero, ge_iff_le]
    obtain ⟨val, property⟩ := x
    linarith
  have : Fintype.card { x // x ∈ s.V } < Fintype.card (Finset.Icc 0 (s.V.card + 1)) :=
  by
    simp_all only [Nat.card_Icc, tsub_zero, Fintype.card_coe, Finset.mem_Icc, zero_le, true_and]
  have : Fintype.card { x // x ∈ s.V } < Fintype.card (Fin (#s.V + 1)) := by
    simp_all only [Nat.card_Icc, tsub_zero, Fintype.card_coe, Finset.mem_Icc, zero_le, true_and, Fintype.card_fin,
      lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt]

  let fe := @Fintype.exists_ne_map_eq_of_card_lt (Fin (s.V.card + 1)) s.V _ _ (λ i=> s.f^[i.val] x) this
  obtain ⟨n1, n2, h⟩ := fe
  use n1, n2
  simp_all only [Nat.card_Icc, tsub_zero, Fintype.card_coe, Finset.mem_Icc, zero_le, true_and, Fintype.card_fin,
    lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, ne_eq, and_true]
  obtain ⟨val, property⟩ := x
  obtain ⟨left, right⟩ := h
  apply Aesop.BuiltinRules.not_intro
  intro a
  simp_all only
  omega

--Theorem outputs a set of magnitude relationships of the above theorem
private lemma iteratef_pigeon_ordered (s : Setup α) (x : s.V) :
  ∃ (n1 n2 : ℕ), n1 < n2 ∧ (s.f^[n1] x) = (s.f^[n2] x) := by
  obtain ⟨n1, n2, hne, heq⟩ := iteratef_pigeon s x
  by_cases h : n1 < n2
  · exact ⟨n1, n2, h, heq⟩
  · have h' : n2 < n1 := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) hne.symm
    simp_all only [ne_eq, not_lt]
    obtain ⟨val, property⟩ := x
    apply Exists.intro
    · apply Exists.intro
      · apply And.intro
        · exact h'
        · simp_all only

  -- Lemma: After iteration multiple times, you will arrive at equivalent sizes of 2 or more.
-- Proof: The nodes n1 and n2 of the lemma above the pigeon nest are the same, and the next node will be nodes that belong to different but same equivalence class.
private lemma iteratef_size2 (s: Setup α) (x: s.V)  : ∃ (n : Nat), 2 ≤ (eqClass_setup s (s.f^[n] x)).card :=
by
  let h := iteratef_pigeon_ordered s x
  /- Another way to break down h.For reference.
  cases h with
  | intro n1 h' =>
    cases h' with
    | intro n2 h'' =>
      cases h'' with
      | intro hneq heq =>
  -/
  obtain ⟨n1, n2, hneq, heq⟩ := h
  let y := s.f^[n1] x
  let z := s.f^[n1+1] x
  have y12: y = s.f^[n2] x := by
    simp_all only [y]
  have fzy: z = s.f y := by
    dsimp [y]
    exact Function.iterate_succ_apply' s.f n1 x
  have neqyz: y ≠ z := by
    intro h
    rw [fzy] at h
    let hnot :=  s.valid y
    rw [Eq.symm h] at hnot
    contradiction
  have : s.pre.le y z := by
    exact f_and_pre s y z (id (Eq.symm fzy))
  have : n2 > n1 + 1:= by
    by_cases n2 = n1 + 1
    case pos h =>
      rw [h] at y12
      rw [h] at hneq
      have : y = s.f (s.f^[n1] x) :=
      by
        exact False.elim (neqyz y12)
      have :y = s.f y := by
        exact this
      have :y ≠ s.f y := by
        exact fun a => neqyz y12
      contradiction
    case neg h =>
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, y, z]
      omega

  have : s.pre.le z y := by
    let ilt := iteratef_lemma_two s x (n1+1) n2 this
    dsimp [y,z]
    simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, ge_iff_le, y, z]
    rwa [← fzy]
  have yineq: y ∈ eqClass_setup s y := by
    simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, y, z]
    rw [eqClass_setup]
    simp_all only [mem_filter, mem_attach, true_and]
    rfl

  have : z ∈ eqClass_setup s y := by
    dsimp [eqClass_setup]
    simp_all only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, mem_attach, y, z]
    ·
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, y, z]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      obtain ⟨val_2, property_2⟩ := z
      symm
      rw [← fzy]
      simp_all only
      symm
      rw [← fzy]
      simp_all only
      induction s
      rename_i h_pre h_setoid po this_2
      subst h_pre h_setoid
      simp_all only [AntisymmRel.setoid_r]
      constructor
      · simp_all only
      · simp_all only
  have : (eqClass_setup s y).card ≥ 2 := by
    dsimp [eqClass_setup]
    simp_all only [Finset.card_filter, Finset.card_univ, true_and, Finset.mem_univ, Finset.mem_filter]
    have hsub : {y, z} ⊆ eqClass_setup s y := by
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, y, z]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      obtain ⟨val_2, property_2⟩ := z
      intro x hx
      simp_all only [Finset.mem_insert, Finset.mem_singleton]
      obtain ⟨val_3, property_3⟩ := x
      cases hx with
      | inl h => simp_all only
      | inr h_1 => simp_all only
    have hsub_card: ({y,z}:Finset s.V).card ≤ (eqClass_setup s y).card := by
      exact Finset.card_le_card hsub
    have :({y,z}:Finset s.V).card = 2:= by
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, Finset.mem_singleton,
        not_false_eq_true, card_insert_of_notMem, Finset.card_singleton, Nat.reduceAdd, y, z]
    rw [this] at hsub_card
    simp
    simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, Finset.mem_singleton,
      not_false_eq_true, card_insert_of_notMem, Finset.card_singleton, Nat.reduceAdd, y, z]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    obtain ⟨val_2, property_2⟩ := z
    exact hsub_card

  use n1

--Definition of the maximum element of s.V assumptions as setup.
def isMaximal (s: Setup α) (a : s.V) : Prop :=
  ∀ b : s.V, s.pre.le a b → s.pre.le b a


private lemma card_ge_two {α : Type} {s : Finset α}
    (h : (2 : ℕ) ≤ s.card) :
    ∃ a b : α, a ∈ s ∧ b ∈ s ∧ a ≠ b :=
by
  have h_pos : 0 < s.card := by
    have : (0 : ℕ) < 2 := by decide
    exact Nat.lt_of_lt_of_le this h
  rcases (Finset.card_pos.mp h_pos) with ⟨a, ha⟩

  have h_card_erase : 1 ≤ (s.erase a).card := by
    have h_eq : (s.erase a).card + 1 = s.card :=
      Finset.card_erase_add_one ha
    have : 2 ≤ (s.erase a).card + 1 := by
      simpa [h_eq] using h
    exact Nat.le_of_succ_le_succ this
  have h_pos_erase : 0 < (s.erase a).card :=
    Nat.succ_le_iff.mp h_card_erase

  rcases (Finset.card_pos.mp h_pos_erase) with ⟨b, hb_in_erase⟩
  rcases (Finset.mem_erase).1 hb_in_erase with ⟨hneq_ba, hb⟩

  exact ⟨a, b, ha, hb, hneq_ba.symm⟩

-----------------------------------------------------------------------

--A lemma is used to prove that equivalence class sizes are 2 or more.
private lemma eqClass_size_ge_two_implies_outside
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α) :
    ∀ y : {x // x ∈ s.V},
      2 ≤ (eqClass_setup s y).card →
      s.f y ∈ eqClass_setup s y :=
by
  intro y hcard

  have htwo : (eqClass_setup s y).card ≥ 2 := hcard
  obtain ⟨a, b, ha, hb, hne⟩ := (card_ge_two htwo)
  set z : {x // x ∈ s.V} :=
    if h : (a : {x // x ∈ s.V}) ≠ y then a else b with hz_def
  have hz_mem : z ∈ eqClass_setup s y := by
    by_cases h : (a : {x // x ∈ s.V}) ≠ y
    · simp [hz_def, h, ha]
    · have : (b : {x // x ∈ s.V}) ≠ y := by
        intro hby
        have : (a : {x // x ∈ s.V}) = b := by
          have : a = y := Subtype.ext (by
            subst hby
            simp_all only
          )
          have : (a : {x // x ∈ s.V}) = (y : {x // x ∈ s.V}) := this
          simpa [hby] using this
        exact (hne this).elim
      simp [hz_def, h, hb, this]

  have hrel : s.setoid.r y z := by
    have := (Finset.mem_filter.mp hz_mem).2
    exact this

  have hle : s.pre.le y z := by
    exact eqClass_le s y z hz_mem
  obtain ⟨n, hn⟩ := iteratef_lemma_ref s y z hle   -- ∃ n, f^[n] y = z
  have hn_pos : 0 < n := by
    by_contra hn0
    have hn00 : n = 0 := by
      exact Nat.eq_zero_of_le_zero (Nat.le_of_not_lt hn0)
    have hzy: z = y := by
      rw [hn00] at hn
      exact id (Eq.symm hn)
    have : z ≠ y := by
      by_cases (a : {x // x ∈ s.V}) ≠ y
      · subst hn00
        simp_all only [ge_iff_le, ne_eq, dite_eq_ite, not_false_eq_true, ↓reduceIte, ↓reduceDIte, z]

      ·
        subst hn00
        simp_all only [ge_iff_le, ne_eq, dite_eq_ite, ↓reduceIte, ↓reduceDIte, Decidable.not_not, Function.iterate_zero,
          id_eq, not_true_eq_false, lt_self_iff_false, not_false_eq_true, z]
    exact this hzy

  have hle_y_fy : s.pre.le y (s.f y) := by
    simpa using f_and_pre s y (s.f y) rfl

  have hle_fy_z : s.pre.le (s.f y) z := by
    have : s.pre.le (s.f y) (s.f^[n - 1] (s.f y)) :=
      iteratef_lemma s (s.f y) (n - 1)

    rw [←@Function.comp_apply _ _ _ (s.f^[n - 1]) s.f ] at this
    rw [←@Function.iterate_succ _ s.f (n-1)] at this
    simp [Nat.sub_add_cancel hn_pos]
    have nsucc: (n-1).succ = n := by
      simp [Nat.sub_add_cancel hn_pos]
    rw [nsucc] at this
    exact le_of_le_of_eq this hn

  have hle_z_y : s.pre.le z y := by
    exact eqClass_ge s y z hz_mem

  have hfy_y : s.pre.le (s.f y) y :=
    s.pre.le_trans (s.f y) z y hle_fy_z hle_z_y
  have hy_fy : s.pre.le y (s.f y) := hle_y_fy

  have hrel_fy : s.setoid.r y (s.f y) := by
    suffices (s.pre.le y (s.f y)) ∧ (s.pre.le (s.f y) y) from by
      rw [s.h_setoid]
      exact this

    simp [hy_fy, hfy_y]

  show s.f y ∈ eqClass_setup s y

  have hmem : (s.f y) ∈ s.V.attach := by
    simp [Finset.mem_attach]    -- automatically true by `.attach`
  have : s.setoid.r y (s.f y) := hrel_fy
  exact Finset.mem_filter.mpr ⟨hmem, this⟩

private lemma cycle_exists
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α) (x : {x // x ∈ s.V})
    (h₂ : 2 ≤ (eqClass_setup s x).card) :
    ∃ p : ℕ, 0 < p ∧ s.f^[p] x = x := by
  have h_fx_in : s.f x ∈ eqClass_setup s x :=
    eqClass_size_ge_two_implies_outside s x h₂
  have h_fx_le_x : s.pre.le (s.f x) x :=
    eqClass_ge s x (s.f x) h_fx_in
  rcases iteratef_lemma_ref s (s.f x) x h_fx_le_x with ⟨m, hm⟩
  refine ⟨m.succ, Nat.succ_pos _, ?_⟩
  exact hm

private lemma iterate_power_cycle
    {α : Type} (f : α → α) (x : α) {p : ℕ}
    (_ : 0 < p) (hcycle : f^[p] x = x) :
    ∀ k : ℕ, f^[p * k] x = x := by
  intro k
  induction k with
  | zero     => exact rfl
  | succ k ih =>
      have hpk: p * (k + 1) = p + p * k := by ring
      have :f^[p*(k+1)] x = f^[p] ((f^[p*k]) x):= by
        rw [←@Function.comp_apply _  _ _ (f^[p]) f^[p*k] x]
        rw [←Function.iterate_add]
        exact congrFun (congrArg (Nat.iterate f) hpk) x

      rw [this]
      simp_all only

-- Points belonging to equivalence classes of size 2 or higher are the largest
--Used in SPO2.The assumption there is: Setup2
theorem eqClass_size_ge_two_implies_inverse
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α) (x : {x // x ∈ s.V})
    (h₂ : 2 ≤ (eqClass_setup s x).card) :
    isMaximal s x := by
  obtain ⟨p, hp_pos, hcycle⟩ := cycle_exists s x h₂
  have hpow := iterate_power_cycle s.f x hp_pos hcycle
  intro y h_xy
  rcases iteratef_lemma_ref s x y h_xy with ⟨n, rfl⟩
  cases n with
  | zero    => simp
  | succ n₀ =>
      let r := (n₀.succ) % p
      have hr_lt : r < p := Nat.mod_lt _ hp_pos
      by_cases hr0 : r = 0
      ·
        have : s.f^[n₀.succ] x = x := by
          have h1 : n₀.succ = p * (n₀.succ / p) := by
            simp_all only [Function.iterate_succ, Function.comp_apply, Nat.succ_eq_add_one, r]
            obtain ⟨val, property⟩ := x
            rw [Nat.mul_div_cancel']
            omega

          rw [h1]
          exact hpow (n₀.succ / p)

        simp [hr0, this]
      ·
        have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
        let m : ℕ := p - r
        have hm_pos : 0 < m := Nat.sub_pos_of_lt hr_lt
        have h_y_step : s.pre.le (s.f^[n₀.succ] x)
                                   (s.f^[m] (s.f^[n₀.succ] x)) :=
          iteratef_lemma s (s.f^[n₀.succ] x) m
        have h_to_x : s.f^[m] (s.f^[n₀.succ] x) = x := by
          have hdecomp : n₀.succ = p * (n₀.succ / p) + r :=
          by
            simp_all only [Function.iterate_succ, Function.comp_apply, Nat.succ_eq_add_one, tsub_pos_iff_lt, r, m]
            obtain ⟨val, property⟩ := x
            rw [Nat.div_add_mod]
          have hsum : n₀.succ + m = p * ((n₀.succ / p) + 1) := by
            have : m = p - r := rfl; simp [m, hdecomp, Nat.add_sub_cancel] at *
            rw [hdecomp]
            calc
              p * ((n₀ + 1) / p) + r + (p - r) = p * ((n₀ + 1) / p) + p :=
              by
                have : r + (p - r) = p := by
                  simp_all only [Nat.add_sub_cancel]
                  refine Nat.add_sub_of_le ?_
                  exact Nat.le_of_succ_le hm_pos
                exact Mathlib.Tactic.Ring.add_pf_add_lt (p * ((n₀ + 1) / p)) this

              _ = p * ((n₀ + 1) / p + 1) :=
              by
                rw [mul_add_one]
              _= p * ((p * ((n₀ + 1) / p) + r) / p + 1) :=
              by
                symm
                exact
                  (Nat.mul_left_cancel_iff hp_pos).mpr
                    (congrFun
                      (congrArg HAdd.hAdd (congrFun (congrArg HDiv.hDiv (id (Eq.symm hdecomp))) p))
                      1)

          have sfsf: s.f^[n₀.succ + m] x =
                  s.f^[p * ((n₀.succ / p) + 1)] x := by
            exact congrFun (congrArg (Nat.iterate s.f) hsum) x
          have := congrArg (fun t => t)
                  (by
                    exact hcycle
                  )

          simp [this, hpow]
          rename_i h1
          rw [←@Function.comp_apply _ _ _ s.f^[n₀] s.f]
          rw [←Function.iterate_succ]
          rw [←@Function.comp_apply _ _ _ s.f^[m] s.f^[n₀.succ]]
          rw [←Function.iterate_add]
          rw [add_comm]
          rw [hsum]
          exact hpow (n₀.succ / p + 1)

        simp [h_to_x]
        exact le_of_le_of_eq h_y_step h_to_x


-------------------------------------------------------------
-- The destination of f with the same equivalent value must be indicated to be equal.I'll use it from outside later.
--Used from TreePartial.
-- Depends on eqClass_size_ge_two_implies_outside.
theorem f_on_equiv
  (s: Setup α) (x y: s.V) (h: s.setoid.r x y) :
  s.setoid.r (s.f x) (s.f y) :=
by
  have eqy: eqClass_setup s x = eqClass_setup s y := by
      apply eqClass_lem
      · rw [s.h_setoid] at h
        rw [setoid_preorder] at h
        simp [equiv_rel] at h
        simp_all only
      · rw [s.h_setoid] at h
        rw [setoid_preorder] at h
        simp [equiv_rel] at h
        simp_all only
  have xineq: x∈ eqClass_setup s x := by
          simp_all only [eqClass_setup]
          simp
          rw [s.h_setoid]
          rw [setoid_preorder]
          simp [equiv_rel]
          rw [s.h_setoid] at h
          rw [setoid_preorder] at h
          simp [equiv_rel] at h
          simp_all only [ge_iff_le, not_le, and_self]

  have yineq: y ∈ eqClass_setup s x := by
      simp_all only [eqClass_setup]
      rw [s.h_setoid] at h
      rw [setoid_preorder] at h
      simp [equiv_rel] at h
      simp_all only [mem_filter, mem_attach, true_and]
      rfl

  by_cases h1: (eqClass_setup s x).card ≥ 2;
  case pos =>
    let eqsx := eqClass_size_ge_two_implies_outside s x h1
    have : s.f x ∈ eqClass_setup s x := by
      simp_all only [eqsx]
      rwa [← eqy]
    have : s.f y ∈ eqClass_setup s y := by
      have :(eqClass_setup s y).card ≥ 2 := by
        rw [←eqy]
        exact h1
      exact eqClass_size_ge_two_implies_outside s y this
    rw [←eqy] at this
    rw [s.h_setoid]
    rw [setoid_preorder]
    simp
    dsimp [equiv_rel]
    let eqe := (eqClass_lem_rev s (s.f x) (s.f y) x)
    specialize eqe eqsx
    specialize eqe this
    constructor
    · exact eqe.1
    · exact eqe.2
  case neg =>
    have :(eqClass_setup s x).card = 1 := by
      have geq1:(eqClass_setup s x).card ≥ 1 := by

        have :(eqClass_setup s x).Nonempty := by
          simp_all only [ge_iff_le, not_le]
          exact ⟨_, xineq⟩
        exact Finset.card_pos.mpr this
      have leq1: (eqClass_setup s x).card  ≤ 1 := by
        simp_all only [ge_iff_le, not_le, one_le_card]
        omega
      exact Eq.symm (Nat.le_antisymm geq1 leq1)

    have :x = y := by
      obtain ⟨xx,hxx⟩ := Finset.card_eq_one.mp this
      rw [hxx] at yineq
      rw [hxx] at xineq
      simp at xineq
      simp at yineq
      rw [←yineq] at xineq
      exact xineq
    subst this
    rfl
