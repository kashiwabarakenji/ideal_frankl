import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Defs
import rooted.CommonDefinition
import rooted.rootedcircuits
import rooted.RootedImplication
import LeanCopilot

open Classical

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
 SF.is_rare v ↔ (including_hyperedges SF v).card <= (deleting_hyperedges SF v).card :=
by
  dsimp [SetFamily.is_rare]
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
  is_no_rooted_vetex SF v → SF.is_rare  v :=
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

--instance vertexorder_is_preorder (SF : ClosureSystem α) [DecidablePred SF.sets]

--頂点を与えると、それと同値な頂点集合全体を返す関数。vertex_orderでなく、vertexorder_is_preorderを使う必要があった。
noncomputable def equivalent_vertex (SF: ClosureSystem α) [DecidablePred SF.sets] (v: SF.ground):Finset SF.ground:=
Finset.filter (fun x => (vertexorder_is_preorder SF).le v x ∧ (vertexorder_is_preorder SF).le x v) SF.ground.attach

--同じ同値類に属する頂点は、同値であり、degreeが等しいことを示す必要がある。
lemma equivalent_vertex_lemma (SF: ClosureSystem α) [DecidablePred SF.sets] (v: SF.ground):
  ∀ x y, x ∈ equivalent_vertex SF v → y ∈ equivalent_vertex SF v → vertex_equiv SF x y :=
by
  dsimp [equivalent_vertex]
  dsimp [vertex_equiv]
  intro x y
  intro hx hy
  simp at hx hy
  constructor
  · exact hx.2.trans hy.1
  · exact hy.2.trans hx.1


lemma minimal_element_is_rare_lemma (SF: ClosureSystem α) [DecidablePred SF.sets] [∀ x, Decidable (∀ y, vertexorder SF x y → y = x)]:
  let RS := rootedSetsFromSetFamily SF.toSetFamily
  --∀ x : SF.ground, --この仮定だとxはいらない。
    ∀ (hp:p ∈ RS.rootedsets),
    let S := Finset.filter (fun s => p.root ∈ s ∧ SF.sets s) SF.toSetFamily.ground.powerset
    let T := Finset.filter (fun s => p.root ∉ s ∧ SF.sets s) SF.toSetFamily.ground.powerset
    let P := equivalent_vertex SF ⟨p.root, (RS.inc_ground p hp).2⟩
   (∀ q ∈ RS.rootedsets, q.stem ∩ (P.image Subtype.val) = ∅ → q.root ∉ (P.image Subtype.val)) →
   (∀ s : S, (s.val \ (P.image Subtype.val)) ∈ T) :=
  by
    intro RS
    --intro x
    intro hp
    intro S T P
    intro hP
    intro H
    dsimp [S, T]
    simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_sdiff, not_and, Decidable.not_not, RS]
    --obtain ⟨xval, xproperty⟩ := x
    obtain ⟨Hval, H_property⟩ := H
    dsimp [S] at H_property
    rw [Finset.mem_filter] at H_property
    simp_all only [Finset.mem_filter, Finset.mem_powerset, forall_const]
    obtain ⟨H_prop, right⟩ := H_property
    obtain ⟨pr_prop, right⟩ := right
    apply And.intro
    · intro y hy
      simp_all only [Finset.mem_sdiff]
      obtain ⟨left_2, right_1⟩ := hy
      exact H_prop left_2
    · apply And.intro
      · simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, not_exists, P]
        apply Exists.intro
        · simp [equivalent_vertex]
        · exact H_prop pr_prop
      · --simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, not_exists, P]
        by_contra h_contra --これで、RootedCircuitsTheorem_includingが使える形に持っていく。
        have arg_lem: p.root ∈ P.image Subtype.val := by
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, not_exists, P]
          apply Exists.intro
          · simp [equivalent_vertex]
          · exact H_prop pr_prop

        simp_all only [and_self, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, P]
        obtain ⟨w, h⟩ := arg_lem

        have arg1:((Hval \ (P.image Subtype.val)).subtype (fun s => s ∈ SF.ground)) ⊆ (Hval.subtype (fun s => s ∈ SF.ground)) :=
        by
          intro y hy
          simp_all only [Finset.mem_subtype, Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right,
            exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]
        have rcti := RootedCircuitsTheorem_including SF ((Hval \ (P.image Subtype.val)).subtype (fun s => s ∈ SF.ground)) (Hval.subtype (fun s => s ∈ SF.ground)) arg1
        have HPreduce:Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) (Hval \ Finset.image Subtype.val P)) = Hval \ (P.image Subtype.val) :=
          by
            ext a : 1
            apply Iff.intro
            · intro a_1
              simp_all [RS]
              intro x
              simp_all only [exists_true_left, not_false_eq_true]
            · intro a_1
              simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
                exists_eq_right_right, and_self, not_false_eq_true, and_true, P]
              simp_all [RS]
              obtain ⟨left, right_1⟩ := a_1
              exact H_prop left
        have :¬SF.sets (Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) (Hval \ Finset.image Subtype.val P))) :=
        by
          rw [HPreduce]
          simp_all only [not_exists, Finset.mem_filter, Finset.mem_powerset, and_self,
            not_false_eq_true, Finset.mem_image, Finset.mem_sdiff, Finset.mem_subtype,
            Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, Finset.coe_mem,
            exists_const, not_and, Decidable.not_not, exists_and_left, not_forall, forall_const]
        let rcti2 := rcti this
        have :SF.sets (Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) Hval)) := by
          have :Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) Hval ) = Hval :=
          by
            ext a : 1
            simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left,
              exists_prop, exists_eq_right_right, and_iff_left_iff_imp]
            intro a_1
            exact H_prop a_1
          rw [this]
          simp_all only
        let rcti3 := rcti2 this
        obtain ⟨root_val, rc_property⟩ := rcti3
        simp at rc_property
        let rc1 := rc_property.1
        obtain ⟨rc12,rc12p⟩ := rc1.2
        let rc3 := rc_property.2.1 rc1.1 rc12
        let rc4 := rc_property.2.2
        simp_all
        --前提は、単にPの中の点ということのようにも思う。結論部分でこの点はrootになる。
        --stemは、H \ Pに含まれている。このようなものは定理の前提に反するので矛盾が導かれるはず。
        have :root_val ∈ Hval → ∀ (x : root_val ∈ SF.ground), ⟨root_val, rc12⟩ ∈ P :=
          by
            intro a
            intro x
            exact rc3
        let rc4' := rc4 this
        simp only [HPreduce] at rc4'
        have lem1:root_val ∈ P.image Subtype.val := by
            simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const, P]
        let stem_val := Hval \ Finset.image Subtype.val P
        have lem2:stem_val ∩ Finset.image Subtype.val P = ∅ := by
            simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const,
              Finset.sdiff_inter_self, P, stem_val]
        have : root_val ∉ stem_val :=
        by
          by_contra h_in
          have :root_val ∈ stem_val ∩ P.image Subtype.val := by
            rw [Finset.mem_inter]
            constructor
            · exact h_in
            · exact lem1
          rw [lem2] at this
          contradiction
        let rcp : ValidPair α := ⟨stem_val, root_val, this⟩
        have rcp_def:  rcp = ⟨stem_val, root_val, this⟩ :=
        by
          ext
          simp
          dsimp [rcp]

        have :root_val ∉ Hval \ Finset.image Subtype.val P := by
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            exists_const, not_false_eq_true]

        have :rcp ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets := by
          dsimp [rcp]
          exact rc4'

        let hpp := hP rcp this lem2
        simp at hpp
        have :root_val ∈ SF.ground := by
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const,
            not_false_eq_true, P, rcp, stem_val]
        let hppp := hpp this
        contradiction

lemma minimal_element_is_rare (SF: ClosureSystem α) [DecidablePred SF.sets] [∀ x, Decidable (∀ y, vertexorder SF x y → y = x)]:
  let RS := rootedSetsFromSetFamily SF.toSetFamily
  ∀ x : SF.ground, (∃ p ∈ RS.rootedsets,  p.root = x ∧ ∃ y : SF.ground, y.val ∈ p.stem ∧ ∃ q ∈ RS.rootedsets, q.root = y.val ∧ q.stem = ({x.val}:Finset α)) →
  SF.is_rare x :=
by
  intro RS
  intro x
  intro h
  simp_all only [Subtype.exists, exists_and_left, exists_prop, RS]
  obtain ⟨val, pr_property⟩ := x
  obtain ⟨p, h⟩ := h
  obtain ⟨p_property, H_right⟩ := h
  obtain ⟨p_subtype, H_right⟩ := H_right
  obtain ⟨w_1, h⟩ := H_right
  obtain ⟨pq_stemroot, w2_right⟩ := h
  obtain ⟨qr_property, q_right⟩ := w2_right
  obtain ⟨q, h⟩ := q_right
  obtain ⟨q_property, q_right⟩ := h
  obtain ⟨q_left_5, q_right⟩ := q_right
  subst q_left_5 p_subtype
  simp_all only
  let P:= equivalent_vertex SF ⟨p.root, pr_property⟩
  have : ∀ s :Finset SF.ground, SF.sets (s.image Subtype.val) → p.root ∈ (s.image Subtype.val) → P ⊆ s :=
  by
    intro s
    intro h1
    intro h2
    --lemma vertex_equiv_hyperedge (SF:ClosureSystem α)[DecidablePred SF.sets]:
    -- ∀ (x y:SF.ground), (vertex_equiv SF) x y → ∀ (s:Finset α), SF.sets s →  (x.val ∈ s ↔ y.val ∈ s) :=
    dsimp [P]
    intro a ha
    have ve: vertex_equiv SF a ⟨p.root, pr_property⟩ := by
      dsimp [equivalent_vertex] at ha
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_true_left,
        Finset.mem_filter, Finset.mem_attach, true_and]
      obtain ⟨val, property_1⟩ := a
      obtain ⟨left_1, right_1⟩ := ha
      rw [vertex_equiv]
      simp_all only
      apply And.intro
      · exact right_1
      · exact left_1
    dsimp [equivalent_vertex] at ha
    have veh := (vertex_equiv_hyperedge SF a ⟨p.root, pr_property⟩ ve (s.image Subtype.val) h1).mpr
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_true_left,
      Finset.mem_filter, Finset.mem_attach, true_and, exists_const, Subtype.coe_eta, Finset.coe_mem, forall_const]
  simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, P]
  --p.rootを含むhyperedge Hから、p.rootを含まないhyperedge H \ Pがhyperedgeであることを示して、さらに単射であることを示せば、rareであることが示せる。
  let S := Finset.filter (fun s => p.root ∈ s ∧ SF.sets s) SF.toSetFamily.ground.powerset
  let T := Finset.filter (fun s => p.root ∉ s ∧ SF.sets s) SF.toSetFamily.ground.powerset
  let i :S → T := fun ss => ⟨(ss.val \ (P.image Subtype.val)), by --この部分を外に出して独立させる。
    have h := ss.property
    simp_all only [Finset.coe_mem, Finset.mem_filter, Finset.mem_powerset, Finset.mem_sdiff, Finset.mem_image,
      Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, not_and, Decidable.not_not, S, T, P]
    obtain ⟨H, property_1⟩ := ss --HがPを含むhyperedge
    simp_all only [Finset.mem_filter, Finset.mem_powerset, forall_const, S]
    apply And.intro
    · simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
      obtain ⟨left, right⟩ := property_1
      obtain ⟨left_1, right⟩ := right
      assumption
      /-
      intro x hx
      simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
        not_exists]
      obtain ⟨left_2, right_1⟩ := hx
      exact left left_2
      -/
    · apply And.intro
      · --show  ⟨p.root, ⋯⟩ ∈ equivalent_vertex SF ⟨p.root, property⟩
        simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
        intro a
        simp_all only
        obtain ⟨left, right⟩ := property_1
        obtain ⟨left_1, right⟩ := right
        simp [equivalent_vertex]
      · dsimp [equivalent_vertex]
        --これが成り立たないとすると、この集合内にstemを持ち、P内にrootが含まれるようなrooted setが存在することになる。
        --すると、Pの定義(equivalent_vertexの定義)に矛盾する。
        --根付き集合の存在定理を使うのか。Aがhyperedgeで、B⊆ Aがhyperedgeでないときは、A-B内に根があり、stemがBに含まれるような根付き集合が存在する。
        --theorem RootedCircuitsTheorem_including (SF : ClosureSystem α)  [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] :
        --  ∀ s : Finset { x // x ∈ SF.ground }, ∀ t : Finset { x // x ∈ SF.ground }, s ⊆ t
        --  → ¬ SF.sets (s.image Subtype.val) → SF.sets (t.image Subtype.val) →
        --    ∃ root ∈ (t \ s).image Subtype.val,∃ stem ⊆ s.image Subtype.val, root ∉ s.image Subtype.val ∧
        --    ((asm:root ∉ s.image Subtype.val ) →
        --  (ValidPair.mk (s.image Subtype.val) root asm) ∈ (rootedSetsSF SF.toSetFamily))
        by_contra h_contra --この条件は、contra3の定義に使うthisの証明で使用済み。
        have : (H.subtype (fun s => s ∈ SF.ground) \ (equivalent_vertex SF ⟨p.root, pr_property⟩)) ⊆ (H.subtype (fun s => s ∈ SF.ground)) :=
        by
          simp_all only [Finset.sdiff_subset]
        have h_contra2 := RootedCircuitsTheorem_including SF (H.subtype (fun s => s ∈ SF.ground) \ (equivalent_vertex SF ⟨p.root, pr_property⟩)) (H.subtype (fun s => s ∈ SF.ground)) this
        have : ¬SF.sets (Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) H \ equivalent_vertex SF ⟨p.root, pr_property⟩)) :=
        by
          have : Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) H \ equivalent_vertex SF ⟨p.root, pr_property⟩) = H \ Finset.image Subtype.val (equivalent_vertex SF ⟨p.root, pr_property⟩) :=
          by
            simp_all
            ext a : 1
            simp_all only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_subtype, Subtype.exists, exists_and_right,
              exists_and_left, exists_eq_right, not_exists, and_congr_right_iff]
            intro a_1
            apply Iff.intro
            · intro a_2 x
              simp_all only [exists_true_left, not_false_eq_true]
            · intro a_2
              simp_all only [not_false_eq_true, exists_prop, and_true]
              simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
              obtain ⟨left, right⟩ := property_1
              obtain ⟨left_1, right⟩ := right
              exact left a_1
          rw [this]
          exact h_contra
        have h_contra3 := h_contra2 this
        clear h_contra2
        have :SF.sets (Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) H)) :=
        by
          simp_all
          have :  (Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) H)) = H :=
          by
            ext a : 1
            simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
              exists_eq_right_right, and_iff_left_iff_imp]
            intro a_1
            simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
            obtain ⟨left, right⟩ := property_1
            obtain ⟨left_1, right⟩ := right
            exact left a_1
          rw [this]
          simp_all only [Finset.mem_filter, Finset.mem_powerset, forall_const, S]
        let h_contra4 := h_contra3 this
        obtain ⟨root, h⟩ := h_contra4
        obtain ⟨cond, right_2⟩ := h
        obtain ⟨stem, right_3⟩ := right_2
        obtain ⟨stem_prop, right_4⟩ := right_3
        simp at cond --rootの満たす条件 これがもともとのhの条件に矛盾するはず。
        have : stem ⊆ H \ (equivalent_vertex SF ⟨p.root, pr_property⟩).image Subtype.val :=
        by
          simp_all only [Finset.subset_iff]
          intro a ha
          simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            not_exists]
          apply And.intro
          · simp_all only [Subtype.forall, Finset.mem_subtype, implies_true, not_and, Decidable.not_not,
            exists_and_left, forall_const, true_and, forall_true_left, exists_const, and_self]
          · intro a_1
            let sp := stem_prop ha
            obtain ⟨aa, aa_property⟩ := sp --使っているっぽい。
            simp_all only [Subtype.forall, Finset.mem_subtype, implies_true, not_and, Decidable.not_not,
              exists_and_left, forall_const, true_and, forall_true_left, exists_const, and_self, not_false_eq_true]

        --(stem,root)の組み合わせに最初の条件を当てはめると、ステムサイズ1の根付き集合が存在することになる。
        --その点は、equivalent_vertex SF ⟨p.root, pr_property⟩に属するのでthisに反する。
        #check cond.2
        obtain ⟨z,zprop⟩ = cond.2.1
  ⟩
        -- 1点の場合と同じようにiの単射性を示して、rareであることを示す。
  have h_inj : Function.Injective i :=
  by
    intros a b hab
    simp only [i] at hab
    simp only [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_image, Finset.disjoint_iff_ne] at hab
    ext x
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, Finset.mem_sdiff, Finset.mem_singleton, not_and, Decidable.not_not, S, T, P]
    constructor
    · intro hx
      by_contra h
      simp_all only [Subtype.mk.injEq, T, S, P]
      obtain ⟨val, property⟩ := a
      obtain ⟨val_1, property_1⟩ := b
      simp_all only
      simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
      obtain ⟨left, right⟩ := property
      obtain ⟨left_1, right_1⟩ := property_1
      obtain ⟨left_2, right⟩ := right
      obtain ⟨left_3, right_1⟩ := right_1
      sorry
    · intro hx
      by_contra h
      simp_all only [Subtype.mk.injEq, T, S, P]
      obtain ⟨val, property⟩ := a
      obtain ⟨val_1, property_1⟩ := b
      simp_all only
      simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
      obtain ⟨left, right⟩ := property
      obtain ⟨left_1, right_1⟩ := property_1
      obtain ⟨left_2, right⟩ := right
      obtain ⟨left_3, right_1⟩ := right_1
      sorry
  sorry
  --exact Finset.card_bij S T i (fun s => (i s).property) h_inj
