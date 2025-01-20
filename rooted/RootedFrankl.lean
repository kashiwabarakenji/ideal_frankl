import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import rooted.rootedcircuits

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
