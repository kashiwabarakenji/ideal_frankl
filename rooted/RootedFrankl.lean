import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Defs
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

    let cstr := ClosureSystemTheorem_mpr_lemma2 SF s h2
    obtain ⟨root, hr⟩ := cstr
    have notin: root.val ∉ Finset.image Subtype.val s := by
      exact hr.2.1
    use ⟨ValidPair.mk (s.image Subtype.val) root.val notin, (by
      simp_all only [Finset.mem_union, Finset.mem_singleton, not_false_eq_true, forall_true_left, true_and]
      obtain ⟨val, property⟩ := v
      obtain ⟨val_1, property_1⟩ := root
      obtain ⟨left, right⟩ := hr
      simp_all only [Subtype.mk.injEq]
      exact right
    )⟩
    --どこかで使っているっぽい
    let svl := sv_lemma SF s v h1 h2 h3
    simp_all only [and_true]
    simp_all only [Finset.mem_union, Finset.mem_singleton, not_false_eq_true, forall_true_left, true_and,
      Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, Finset.coe_mem,
      exists_const, false_or]

--lemma ClosureSystemTheorem_mpr_lemma2 (SF : ClosureSystem α)  [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] :
-- ∀ s : Finset { x // x ∈ SF.ground }, ¬ SF.sets (s.image Subtype.val) → ∃ root ∈ (closure_operator_from_SF SF).cl s,
--root.val ∉ s.image Subtype.val ∧ ((asm:root.val ∉ s.image Subtype.val ) →
--(ValidPair.mk (s.image Subtype.val) root.val asm) ∈ (rootedSetsSF SF.toSetFamily))

--このあとは、頂点vに根がないときは、rareなことの証明に向かう。単射の構成と、単射性の証明。
lemma injective_lemma (SF: ClosureSystem α) [DecidablePred SF.sets] (s:Finset SF.ground)(v: SF.ground):
  is_no_rooted_vetex SF v → v ∉ s → SF.sets ((s.image Subtype.val) ∪ {v.val}) → SF.sets (s.image Subtype.val)   :=
by
  intro no_root
  intro h1 h2
  by_contra h3
  let ers := exists_rooted_set SF s v h1 h3 h2
  obtain ⟨p, hp⟩ := ers
  dsimp [is_no_rooted_vetex] at no_root
  exact no_root.2 p hp.1

--写像を定義し、定義域にはいっていることを証明。Injectionであることの証明は別の定理。
def injective_v  (SF: ClosureSystem α) (v: SF.ground) [DecidablePred SF.sets] (noroot: is_no_rooted_vetex SF v): including_hyperedges SF.toSetFamily v → deleting_hyperedges SF.toSetFamily v :=
  fun ss => ⟨ss.val \ {v.val}, by
    have h := ss.property
    simp only [including_hyperedges, Finset.mem_filter] at h
    simp only [deleting_hyperedges, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton, h, true_and, not_true, false_and]
    constructor
    · --終域に入っていること。
      simp_all only [Finset.mem_powerset]
      obtain ⟨val, property⟩ := v
      obtain ⟨val_1, property_1⟩ := ss
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      simp_all only
      simp_all only
      intro x hx
      simp_all only [Finset.mem_sdiff, Finset.mem_singleton]
      obtain ⟨left_2, right_1⟩ := hx
      exact left left_2

    · --goal SF.sets (↑ss \ {↑v})
      simp
      dsimp [including_hyperedges] at ss

      let sss := (ss.val \ {v.val}).subtype (fun s => s ∈ SF.ground)
      have notin:v ∉ sss := by
        dsimp [sss]
        simp

      have sets_ss : SF.sets ((sss.image Subtype.val) ∪ {v.val}) :=
      by
        dsimp [sss]
        simp_all only [Finset.mem_powerset, Finset.mem_subtype, Finset.mem_sdiff, Finset.mem_singleton,
          not_true_eq_false, and_false, not_false_eq_true, sss]
        obtain ⟨val, property⟩ := v
        obtain ⟨val_1, property_1⟩ := ss
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        simp_all only
        have :Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) (val_1 \ {val})) ∪ {val} = Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) val_1) :=
        by
          ext a : 1
          simp_all only [Finset.mem_union, Finset.mem_image, Finset.mem_subtype, Finset.mem_sdiff,
            Finset.mem_singleton, Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right]
          apply Iff.intro
          · intro a_1
            cases a_1 with
            | inl h => simp_all only [and_self]
            | inr h_1 =>
              subst h_1
              simp_all only [and_self]
          · intro a_1
            simp_all only [true_and, and_true]
            obtain ⟨left_2, right_1⟩ := a_1
            tauto
        rw [this]
        convert right
        ext a : 1
        simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
          exists_eq_right_right, and_iff_left_iff_imp]
        intro a_1
        exact left a_1

      convert injective_lemma SF sss   v noroot notin sets_ss
      dsimp [sss]
      simp_all only [Finset.mem_powerset, Finset.mem_subtype, Finset.mem_sdiff, Finset.mem_singleton,
        not_true_eq_false, and_false, not_false_eq_true, sss]
      obtain ⟨val, property⟩ := v
      obtain ⟨val_1, property_1⟩ := ss
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      simp_all only
      ext a : 1
      simp_all only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_image, Finset.mem_subtype, Subtype.exists,
        exists_and_left, exists_prop, exists_eq_right_right, iff_self_and, and_imp]
      intro a_1 a_2
      exact left a_1
  ⟩

--単射性の証明。Lean Copilotに任せたら、証明が長くなった。
lemma exists_injection
(SF: ClosureSystem α) [DecidablePred SF.sets] (v: SF.ground) (noroot: is_no_rooted_vetex SF v):
   Function.Injective (injective_v SF v noroot) :=
by
  intro s1 s2
  dsimp [injective_v]
  intro h
  simp at h
  have hs1: v.val ∈ s1.val :=
  by
    obtain ⟨val, property⟩ := v
    obtain ⟨val_1, property_1⟩ := s1
    simp_all only
    dsimp [including_hyperedges] at property_1
    simp_all only [Finset.mem_filter, Finset.mem_powerset]
  have hs2: v.val ∈ s2.val :=
  by
    obtain ⟨val, property⟩ := v
    obtain ⟨val_1, property_1⟩ := s2
    simp_all only
    dsimp [including_hyperedges] at property_1
    simp_all only [Finset.mem_filter, Finset.mem_powerset]

  ext x
  obtain ⟨val, property⟩ := v
  obtain ⟨val_1, property_1⟩ := s1
  obtain ⟨val_2, property_2⟩ := s2
  simp_all only
  simp_all only

  apply Iff.intro
  · intro a
    by_cases h1: x = val
    case pos =>
      subst x
      have h2: val ∈ val_2 := by
        simp_all only
      exact hs2
    case neg =>
      have h2: x ∈ val_1 := by
        simp_all only
      have h3: x ∈ val_1 \ {val} :=
      by
        rw [Finset.mem_sdiff]
        simp_all only [Finset.mem_singleton, not_false_eq_true, and_self]
      simp_all only [Finset.mem_sdiff, Finset.mem_singleton, not_false_eq_true, and_true]

  · intro a
    by_cases h1: x = val
    case pos =>
      subst x
      have h2: val ∈ val_1 := by
        simp_all only
      exact hs1
    case neg =>
      have h2: x ∈ val_2 := by
        simp_all only
      have h3: x ∈ val_2 \ {val} :=
      by
        rw [Finset.mem_sdiff]
        simp_all only [Finset.mem_singleton, not_false_eq_true, and_self]
      have h4: x ∈ val_1 \ {val} :=
      by
        rw [←h] at h3
        simp_all only [Finset.mem_sdiff, Finset.mem_singleton, not_false_eq_true, and_self]
      rw [Finset.mem_sdiff] at h4
      simp_all only [Finset.mem_sdiff, not_false_eq_true, and_self, Finset.mem_singleton, and_true]

--主定理。根がない頂点は、rareな頂点になる。
theorem noroot_vertex_is_rare (SF: ClosureSystem α) [DecidablePred SF.sets] (v: SF.ground):
  is_no_rooted_vetex SF v → is_rare SF.toSetFamily v :=
by
  intro noroot
  rw [rare_and_card]
  let ei := @exists_injection _ _ _ SF _ v noroot

  let S := (including_hyperedges SF.toSetFamily v)
  let T := (deleting_hyperedges SF.toSetFamily v)

  let f := injective_v SF v noroot

  have h_inj : Function.Injective f :=
  by
    dsimp [f]
    exact ei

  have h_inj2: Set.InjOn f ↑S.attach :=
  by
    dsimp [Set.InjOn]
    dsimp [Function.Injective] at h_inj
    intro a ha b hb
    apply h_inj

  -- injective_v の結果が deleting_hyperedges に属することを示す
  have h_f_image : ∀ s : { x // x ∈ S }, (f s) ∈ T.attach := by
    intro s
    simp_all only [Finset.mem_attach, f, ei, T]

  have h_f_image2: ∀ a ∈ S.attach, f a ∈ T.attach := by
    intro a a_1
    simp_all only [Finset.mem_attach, implies_true, f, ei, S, T]

  --型推論がうまくいかず@を利用して、かなり強引に引数の形を合わせたが、よく理解してない部分もある。
  let fi := @Finset.card_le_card_of_injOn S T S.attach T.attach f h_f_image2 h_inj2
  dsimp [S, T] at fi
  simp_all only [Finset.mem_attach, implies_true, ge_iff_le, f, ei, S, T]
  obtain ⟨val, property⟩ := v
  simp_all only
  convert fi
  · simp_all only [Finset.card_attach]
  · simp_all only [Finset.card_attach]
