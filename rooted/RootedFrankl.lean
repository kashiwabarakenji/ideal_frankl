import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import rooted.rootedcircuits
import LeanCopilot

variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def is_no_rooted_vetex (SF: ClosureSystem α) [DecidablePred SF.toSetFamily.sets] (v: α):Prop:=
v ∈ SF.ground ∧ ∀(p : (rootedSetsFromSetFamily SF.toSetFamily).rootedsets), p.val.root ≠ v

noncomputable def including_hyperedges (SF: SetFamily α) [DecidablePred SF.sets] (v: α):Finset (Finset α):=
SF.ground.powerset.filter (fun s => v ∈ s ∧ SF.sets s)

noncomputable def deleting_hyperedges (SF: SetFamily α) [DecidablePred SF.sets] (v: α):Finset (Finset α):=
SF.ground.powerset.filter (fun s => v ∉ s ∧ SF.sets s)

omit [Fintype α] in
lemma total_card (SF: SetFamily α) [DecidablePred SF.sets] (v: α):
(including_hyperedges SF v).card + (deleting_hyperedges SF v).card= SF.number_of_hyperedges :=
by
  dsimp [SetFamily.number_of_hyperedges]
  dsimp [including_hyperedges,deleting_hyperedges]
  let ss := SF.ground.powerset.filter (fun s => SF.sets s)
  have h := @Finset.filter_card_add_filter_neg_card_eq_card _ ss (fun s => v ∈ s) _ _
  dsimp [ss] at h
  simp at h
  simp only [←h]
  simp
  have term1:Finset.filter (fun s => v ∈ s ∧ SF.sets s) SF.ground.powerset = Finset.filter (fun s => v ∈ s) (Finset.filter (fun s => SF.sets s) SF.ground.powerset) :=
  by
    ext a : 1
    simp_all only [Finset.mem_filter, Finset.mem_powerset]
    apply Iff.intro
    · intro a_1
      simp_all only [and_self]
    · intro a_1
      simp_all only [and_self]
  have term2: Finset.filter (fun s => v ∉ s ∧ SF.sets s) SF.ground.powerset = Finset.filter (fun s => v ∉ s) (Finset.filter (fun s => SF.sets s) SF.ground.powerset) :=
  by
    ext a : 1
    simp_all only [Finset.mem_filter, Finset.mem_powerset]
    apply Iff.intro
    · intro a_1
      simp_all only [and_self, not_false_eq_true]
    · intro a_1
      simp_all only [and_self, not_false_eq_true]
  simp_all only

omit [Fintype α] in
lemma rare_and_card (SF: SetFamily α) [DecidablePred SF.sets] (v: α):
 is_rare SF v ↔ (including_hyperedges SF v).card <= (deleting_hyperedges SF v).card :=
by
  dsimp [is_rare]
  rw [←total_card SF v]
  dsimp [including_hyperedges, deleting_hyperedges]
  dsimp [SetFamily.degree]
  simp_all only [tsub_le_iff_right, zero_add]
  have :Finset.filter (fun s => SF.sets s ∧ v ∈ s) = Finset.filter (fun s =>  v ∈ s ∧ SF.sets s) :=
  by
    ext x a : 2
    simp_all only [Finset.mem_filter, and_congr_right_iff]
    intro a_1
    apply Iff.intro
    · intro a_2
      simp_all only [and_self]
    · intro a_2
      simp_all only [and_self]

  rw [this]

  apply Iff.intro
  · intro a
    simp at a
    linarith

  · intro a
    simp at a
    linarith

omit [Fintype α] in
lemma ssubset_lem (s t : Finset α) (v : α) (h1 : s ⊂ t) (h2 : t ⊆ s ∪ {v}) : t = s ∪ {v} :=
by
  -- 真部分集合の定義より、s ⊆ t かつ s ≠ t
  have h3 : s ⊆ t := by
    rw [Finset.ssubset_def] at h1
    simp_all only
  have h4 : s ≠ t := by
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only [Finset.subset_union_left, subset_refl]
    rw [Finset.ssubset_def] at h1
    simp_all only [subset_refl, not_true_eq_false, and_false]

  -- v が t に含まれていることを示す
  have hv_in_t : v ∈ t :=
    by
      by_contra hv_not_in_t
      -- 仮定より t ⊆ s ∪ {v}
      -- v ∉ t より t ⊆ s が成り立つ
      have h_t_subset_s : t ⊆ s := by
        rw [Finset.union_comm] at h2
        rw [Finset.subset_iff]
        rw [Finset.subset_iff] at h2
        intro x hx
        simp_all only [Finset.mem_union, Finset.mem_singleton, ne_eq]
        obtain h | h := h2 hx
        · subst h
          simp_all only
        · simp_all only
      exact h4 (Finset.Subset.antisymm h3 h_t_subset_s)

  -- s ∪ {v} ⊆ t を示す
  have h_s_union_v_subset_t : s ∪ {v} ⊆ t :=
    by
      intros x hx
      cases Finset.mem_union.1 hx with
      | inl hs => exact h3 hs
      | inr hv =>
        have : v ∈ t := hv_in_t
        simp_all only [ne_eq, Finset.mem_union, or_true, Finset.mem_singleton]

  -- s ∪ {v} = t を示す
  exact Finset.Subset.antisymm h2 h_s_union_v_subset_t

lemma sv_lemma (SF: ClosureSystem α) [DecidablePred SF.sets] (s:Finset SF.ground)(v: SF.ground):
 v ∉ s → ¬ SF.sets (s.image Subtype.val)  → SF.sets ((s.image Subtype.val) ∪ {v.val}) → (closure_operator_from_SF SF).cl s = s ∪ {v} :=
by
  intro h1 h2 h3
  have h5: SF.sets (Finset.image Subtype.val (s ∪ {v})) := by
      rw [Finset.image_union]
      exact h3
  have h1: (closure_operator_from_SF SF).cl (s ∪ {v}) = s ∪ {v} := by

    let idem := idempotent_from_SF_finset_lem SF (s ∪ {v}) h5
    obtain ⟨val, property⟩ := v
    simp_all only
    exact idem

  --lemma closure_monotone_lemma {α : Type} [DecidableEq α] [Fintype α] (F : ClosureSystem α)[DecidablePred F.sets] (s : Finset F.ground) (t : Finset F.ground) :
  --F.sets (t.image Subtype.val) → s ⊆ t → (closure_operator_from_SF F).cl s ⊆ t :=
  let cml := closure_monotone_lemma SF s (s ∪ {v}) h5 (by simp)

  have h6: (closure_operator_from_SF SF).cl s = s ∪ {v} := by
    apply ssubset_lem s ((closure_operator_from_SF SF).cl s) v
    · rw [Finset.ssubset_def]
      constructor
      exact (closure_operator_from_SF SF).extensive s
      contrapose h2
      simp at h2
      have : (closure_operator_from_SF SF).cl s = s :=
      by
        have : s ⊆ (closure_operator_from_SF SF).cl s :=
        by
          exact (closure_operator_from_SF SF).extensive s
        exact Finset.Subset.antisymm h2 this
      exact not_not_intro (idempotent_from_SF_finset_lem_mpr SF s this)
    · exact cml
  simp_all only

  lemma exists_rooted_set (SF: ClosureSystem α) [DecidablePred SF.sets] (s:Finset SF.ground)(v: SF.ground):
  v ∉ s → ¬ SF.sets (s.image Subtype.val)  → SF.sets ((s.image Subtype.val) ∪ {v.val})→
  ∃(p : (rootedSetsFromSetFamily SF.toSetFamily).rootedsets), p.val.root = v.val ∧ p.val.stem = s.image Subtype.val :=
  by
    intro h1 h2 h3
    let svl := sv_lemma SF s v h1 h2 h3
    set RS := rootedSetsFromSetFamily SF.toSetFamily with RS_def
    have :rootedsetToClosureSystem RS = SF := by
      sorry
    have arg:Finset.image Subtype.val s ⊆ SF.ground := by
      simp_all only [RS]
      obtain ⟨val, property⟩ := v
      simp [Finset.image_subset_iff]
    let rcs := (rootedcircuits_setfamily RS SF this (s.image Subtype.val) arg).mp h2
    obtain ⟨p, h4⟩ := rcs
    search_proof
