--主に頂点がrareになるための条件の定理を証明する。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Defs
import rooted.CommonDefinition
import rooted.RootedCircuits
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

--単射性と、rareの関係に関係する補題
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

--equivaent_vertexであれば、parallelであることも示す。parallelなので、次数が等しくなるし、1元を含めば、他のparallelな元も含む。
lemma equivalent_vertex_parallel (SF: ClosureSystem α) [DecidablePred SF.sets] (v: SF.ground):
  ∀ x:SF.ground, x ∈ equivalent_vertex SF v → x ≠ v  → parallel SF x v :=
by
  intro x hx
  intro xneqv
  dsimp [parallel]
  dsimp [equivalent_vertex] at hx
  dsimp [vertexorder_is_preorder] at hx
  dsimp [vertexorder] at hx
  simp_all only [Finset.mem_filter, Finset.mem_attach, true_and, Finset.coe_mem]
  obtain ⟨val, property⟩ := v
  obtain ⟨val_1, property_1⟩ := x
  simp_all only [ne_eq, Subtype.mk.injEq, not_false_eq_true, true_and]
  intro s a
  apply Iff.intro
  · intro a_1
    simp_all only
  · intro a_1
    simp_all only

lemma equivalent_vertex_set_lemma (SF: ClosureSystem α) [DecidablePred SF.sets]:
  ∀ x : SF.ground,
  let P := equivalent_vertex SF ⟨x.val, x.property⟩
  (∀ s : Finset SF.ground, SF.sets (s.image Subtype.val) → x ∈ s → P ⊆ s) :=
by
  simp
  intro x hx
  intro s hset hs
  intro y hy
  by_cases h1: y = x
  case pos =>
    subst h1
    simp_all only [Subtype.coe_eta]
  case neg =>
    have h2: y ≠ ⟨x, hx⟩ := by
      intro h2
      subst h2
      simp_all only [not_true_eq_false]
    let evp := equivalent_vertex_parallel SF ⟨x,hx⟩ y hy h2
    dsimp [parallel] at evp
    have :x ∈ s.image Subtype.val := by
      simp_all only [not_false_eq_true, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
        exists_const, evp]
    let evp2 := (evp.2.2 (s.image Subtype.val) hset ).mpr this
    rw [Finset.mem_image] at evp2
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const,
      exists_true_left]

lemma minimal_element_is_rare_lemma (SF: ClosureSystem α) [DecidablePred SF.sets] :
  let RS := rootedSetsFromSetFamily SF.toSetFamily
    ∀ x : SF.ground,
    let S := Finset.filter (fun s => x.val ∈ s ∧ SF.sets s) SF.toSetFamily.ground.powerset
    let T := Finset.filter (fun s => x.val ∉ s ∧ SF.sets s) SF.toSetFamily.ground.powerset
    let P := equivalent_vertex SF ⟨x.val, x.property⟩
   (∀ q ∈ RS.rootedsets, q.root = x → q.stem ∩ (P.image Subtype.val) ≠ ∅) → --q.root ∉ (P.image Subtype.val)) →
   (∀ s : S, (s.val \ (P.image Subtype.val)) ∈ T) :=
  by
    intro RS
    intro x
    intro S T P
    intro hP
    intro H
    dsimp [S, T]
    simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_sdiff, not_and, Decidable.not_not, RS]
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
      · --
        by_contra h_contra --これで、RootedCircuitsTheorem_closureが使える形に持っていく。
        have arg_lem: x.val ∈ P.image Subtype.val := by
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
        --theorem RootedCircuitsTheorem_closure (SF : ClosureSystem α)  [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (x:SF.ground):
        -- ∀ s : Finset { x // x ∈ SF.ground }, x ∈ closureOperator SF s
        --  → ¬ SF.sets (s.image Subtype.val)  →
        --  (asm:↑x ∉ Finset.image Subtype.val s) →
        --  (ValidPair.mk (s.image Subtype.val) x asm) ∈ (rootedSetsSF SF.toSetFamily) :=
        have rcti := RootedCircuitsTheorem_closure SF x  (Hval.subtype (fun s => s ∈ SF.ground) \  P)
        have : x ∈ closureOperator SF (Hval.subtype (fun s => s ∈ SF.ground) \  P):=
        by
          have :¬SF.sets (Finset.image Subtype.val (Hval.subtype (fun s => s ∈ SF.ground) \  P)) :=
          by
            dsimp [P]
            convert h_contra
            simp_all [P]
            simp_all only
            obtain ⟨val, property⟩ := x
            simp_all only
            ext a : 1
            simp_all only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_subtype, Subtype.exists, exists_and_right,
              exists_and_left, exists_eq_right, not_exists, and_congr_right_iff]
            intro a_1
            apply Iff.intro
            · intro a_2 x
              simp_all only [exists_true_left, not_false_eq_true]
            · intro a_2
              simp_all only [not_false_eq_true, exists_prop, and_true]
              exact H_prop a_1
          let scs := closure_ssubset SF (Hval.subtype (fun s => s ∈ SF.ground) \  P) this
          let scse := Finset.exists_of_ssubset scs
          obtain ⟨v, v_prop⟩ := scse

          have: v.val ∈ Hval :=
          by
            let cml := closure_monotone_lemma SF (Hval.subtype (fun s => s ∈ SF.ground) \  P) (Hval.subtype (fun s => s ∈ SF.ground))
            have :SF.sets (Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) Hval)) :=
            by
              have :Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) Hval ) = Hval :=
              by
                ext a : 1
                simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left,
                  exists_prop, exists_eq_right_right, and_iff_left_iff_imp]
                intro a_1
                exact H_prop a_1
              rw [this]
              simp_all only
            let cml2 := cml this
            have :Finset.subtype (fun s => s ∈ SF.ground) Hval \ P ⊆ Finset.subtype (fun s => s ∈ SF.ground) Hval :=
            by
              simp_all only [Subtype.coe_eta, ne_eq, Finset.mem_filter, Finset.mem_powerset,
                and_self, not_false_eq_true, Finset.mem_image, Finset.mem_sdiff, Finset.mem_subtype,
                Subtype.exists, exists_and_right, exists_and_left, exists_eq_right,
                not_true_eq_false, exists_const, and_false, forall_true_left, forall_const, not_and,
                Decidable.not_not, Finset.sdiff_subset]

            let cml3 := cml2 this

            have : v ∈ Finset.subtype (fun s => s ∈ SF.ground) Hval :=
            by
              let cml4 := cml3 v_prop.1
              exact cml4


            simp_all only [Subtype.coe_eta, ne_eq, Finset.mem_filter, Finset.mem_powerset, and_self, not_false_eq_true,
              Finset.mem_image, Finset.mem_sdiff, Finset.mem_subtype, Subtype.exists, exists_and_right,
              exists_and_left, exists_eq_right, not_true_eq_false, exists_const, and_false, forall_true_left,
              forall_const, and_true, P]


          have vinP: v ∈ P :=
          by
            dsimp [P]
            simp_all only [Subtype.coe_eta, ne_eq, Finset.mem_filter, Finset.mem_powerset, and_self,
              not_false_eq_true, Finset.mem_image, Finset.mem_sdiff, Finset.mem_subtype, Subtype.exists,
              exists_and_right, exists_and_left, exists_eq_right, not_true_eq_false, exists_const, and_false,
              forall_true_left, forall_const, true_and, Decidable.not_not, P]

          have : x ∈ Finset.subtype (fun s => s ∈ SF.ground) Hval :=
          by
            simp_all only [Finset.mem_subtype]

          have xinP: x ∈ P :=
          by
            simp_all only [Subtype.coe_eta, ne_eq, Finset.mem_filter, Finset.mem_powerset, and_self,
              not_false_eq_true, Finset.mem_image, Finset.mem_sdiff, Finset.mem_subtype, Subtype.exists,
              exists_and_right, exists_and_left, exists_eq_right, not_true_eq_false, exists_const, and_false,
              forall_true_left, forall_const, not_and, Decidable.not_not, P]

          --xとvはparallelで、vはclosureの元なので、xもclosureの元。closureはhyperedgeであることも使う。
          have para: v ≠ x → parallel SF v x :=
          by
            intro xneqv
            simp [P] at vinP
            simp [P] at xinP
            exact equivalent_vertex_parallel SF x v vinP xneqv

          have sfs:SF.sets ((closureOperator SF (Finset.subtype (fun s => s ∈ SF.ground) Hval \ P)).image Subtype.val) :=
          by
            let idm := closureOperator_image_in_sets SF (Finset.subtype (fun s => s ∈ SF.ground) Hval \ P)
            simp_all only [Subtype.coe_eta, ne_eq, Finset.mem_filter, Finset.mem_powerset, and_self, not_false_eq_true,
              Finset.mem_image, Finset.mem_sdiff, Finset.mem_subtype, Subtype.exists, exists_and_right,
              exists_and_left, exists_eq_right, not_true_eq_false, exists_const, and_false, forall_true_left,
              forall_const, and_true, P, idm]

          by_cases h2: x = v
          case pos =>
            rw [h2]
            subst h2
            simp_all only [Subtype.coe_eta, ne_eq, Finset.mem_filter, Finset.mem_powerset, and_self,
              not_false_eq_true, Finset.mem_image, Finset.mem_sdiff, Finset.mem_subtype,
              Subtype.exists, exists_and_right, exists_and_left, exists_eq_right, not_true_eq_false,
              exists_const, and_false, forall_true_left, forall_const, and_true, IsEmpty.forall_iff]
          case neg =>
            let para2 := para (Ne.symm h2)
            let equ := equivalent_vertex_set_lemma SF v (closureOperator SF (Finset.subtype (fun s => s ∈ SF.ground) Hval \ P)) sfs v_prop.1
            dsimp [P] at xinP
            have : x ∈ equivalent_vertex SF v :=
            by
              dsimp [equivalent_vertex]
              rw [Finset.mem_filter]
              dsimp [P] at vinP
              dsimp [equivalent_vertex] at vinP
              rw [Finset.mem_filter] at vinP
              simp_all only [and_self, forall_true_left, Finset.mem_attach]
            simp_all [P]
            simp_all only
            apply equ
            simp_all only

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

        let rcti2 := rcti this
        have :¬SF.sets (Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) (Hval \ Finset.image Subtype.val P))) :=
        by
          rw [HPreduce]
          simp_all only [not_false_eq_true, Subtype.exists,exists_const]--
        have :¬SF.sets (Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) Hval \ P)) :=
        by
           convert this
           simp_all only [Subtype.coe_eta, ne_eq, Finset.mem_filter, Finset.mem_powerset, and_self, not_false_eq_true,
             P]
           simp_all only [Finset.coe_mem]
           obtain ⟨val, property⟩ := x
           simp_all only
           ext a : 1
           simp_all only [Finset.mem_sdiff, Finset.mem_subtype, Finset.mem_image, Subtype.exists, exists_and_right,
             exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]

        let rcti3 := rcti2 this

        have :↑x ∉ Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) Hval \ P) :=
        by
          simp_all only [not_false_eq_true, Finset.mem_image, Finset.mem_sdiff,
            Subtype.exists, exists_and_right,  exists_eq_right, not_true_eq_false,exists_const, and_false]--
        let rcti4 := rcti3 this
        simp at rcti4
        dsimp [rootedSetsSF] at rcti4
        dsimp [allCompatiblePairs] at rcti4
        simp at rcti4

        let stem_val := Finset.image Subtype.val (Finset.subtype (fun s => s ∈ SF.ground) Hval \ P)
        let root_val := x.val
        let rcp : ValidPair α := ⟨stem_val, root_val, this⟩

        have :rcp ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets :=
        by
          dsimp [rcp]
          dsimp [rootedSetsFromSetFamily]
          simp_all only [Subtype.coe_eta, ne_eq, Finset.mem_filter, Finset.mem_powerset]

        let hpp := hP rcp this

        have: rcp.root = ↑x :=
        by
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, Subtype.coe_eta,not_false_eq_true]
        let hpp2 := hpp this

        have :stem_val ∩ Finset.image Subtype.val (equivalent_vertex SF x) = ∅ := by
          dsimp [stem_val]
          dsimp [P]
          simp
          by_contra h_in
          rw [←Finset.not_nonempty_iff_eq_empty] at h_in
          rw [not_not] at h_in
          obtain ⟨val, property⟩ := h_in
          simp_all only [Finset.mem_inter, Finset.mem_image, Finset.mem_sdiff,Subtype.exists, exists_and_right,  exists_eq_right]
          obtain ⟨left_1, right_2⟩ := property
          obtain ⟨left_1, right_3⟩ := left_1
          obtain ⟨w, h_1⟩ := right_2
          obtain ⟨w_1, h_2⟩ := right_3
          simp_all only

        contradiction

--injectiveとrareの関係だが、このファイルの上にある補題のtotal_cardと内容が同じだった。
omit [Fintype α] [DecidableEq α] in
theorem card_decomp [DecidableEq α] (SF : SetFamily α)[DecidablePred SF.sets] (x : α) :
    (Finset.filter (fun s => SF.sets s) SF.ground.powerset).card
  = (Finset.filter (fun s => x ∈ s ∧ SF.sets s) SF.ground.powerset).card
  + (Finset.filter (fun s => x ∉ s ∧ SF.sets s) SF.ground.powerset).card :=
by
  -- T := 「SF.sets を満たす s」だけを取り出したフィンセット
  let T := Finset.filter (fun s => SF.sets s) SF.ground.powerset

  -- まず T を「x ∈ s」かどうかで分割する
  let ST := Finset.filter (fun s => SF.sets s) SF.ground.powerset
  have h := @Finset.filter_card_add_filter_neg_card_eq_card _ ST (fun s => x ∈ s) _ _
  dsimp [ST] at h
  rw [ Finset.filter_filter,  Finset.filter_filter] at h
  rw [h.symm]
  ring_nf
  congr
  ext x_1 : 2
  apply Iff.intro
  · intro a
    simp_all only [and_self]
  · intro a
    simp_all only [and_self]
  ext x_1 : 2
  apply Iff.intro
  · intro a
    simp_all only [not_false_eq_true, and_self]
  · intro a
    simp_all only [not_false_eq_true, and_self]

--rare_and_cardと同じ内容だった。rare_and_cardのほうが必要十分条件なので推奨。
lemma injection_rare_lemma (SF: ClosureSystem α) [DecidablePred SF.sets] :
    ∀ x : SF.ground,
    let S := Finset.filter (fun s => x.val ∈ s ∧ SF.sets s) SF.toSetFamily.ground.powerset
    let T := Finset.filter (fun s => x.val ∉ s ∧ SF.sets s) SF.toSetFamily.ground.powerset
    (∃ i : S → T, ∀ s1 s2, i s1 = i s2 → s1 = s2) →
    SF.is_rare x :=
by
  intro x
  intro S T
  intro h1
  obtain ⟨i, h2⟩ := h1
  have haa: ∀ a ∈ S.attach, i a ∈ T.attach :=
  by
    intro a ha
    simp at ha
    simp

  have :Set.InjOn i ↑S.attach :=
  by
    dsimp [Set.InjOn]
    intro a ha b hb
    intro h
    exact h2 ⟨a,a.property⟩ ⟨b,b.property⟩ h

  have : S.card ≤ T.card :=
  by
    let c1 := @Finset.card_le_card_of_injOn S T S.attach T.attach i haa this
    rw [Finset.card_attach, Finset.card_attach] at c1
    exact c1

  dsimp [SetFamily.is_rare]
  have :SF.number_of_hyperedges  = S.card + T.card :=by
    dsimp [SetFamily.number_of_hyperedges]
    dsimp [S, T]
    let cd := card_decomp SF.toSetFamily x
    simp_all only [Subtype.forall, Finset.mem_filter, Finset.mem_powerset, Nat.cast_add]

  dsimp [SetFamily.degree]
  dsimp [SetFamily.number_of_hyperedges]
  dsimp [S, T] at this
  dsimp [SetFamily.number_of_hyperedges] at this
  have sub1: ↑(Finset.filter (fun s => SF.sets s ∧ x.val ∈ s)) = ↑(Finset.filter (fun s => x.val ∈ s ∧ SF.sets s)) :=
  by
    ext x_1 : 1
    simp only [Finset.mem_filter, and_comm]

  rw [sub1]
  linarith [this]

--根付き集合がある条件を満たせばrareになる。重要な定理。
theorem element_is_rare_rootedset (SF: ClosureSystem α) [DecidablePred SF.sets] [∀ x, Decidable (∀ y, vertexorder SF x y → y = x)]:
  let RS := rootedSetsFromSetFamily SF.toSetFamily
    ∀ x : SF.ground,
   let P := equivalent_vertex SF ⟨x.val, x.property⟩
   (∀ r ∈ RS.rootedsets, r.root = x → r.stem ∩ (P.image Subtype.val) ≠ ∅)  →
   SF.is_rare x :=

by
  intro RS
  intro x
  intro P
  intro h1 --h1の仮定にあるzは、xと同値な頂点である。よって、z in Pとなる。よって、xを根とする任意のrooted setは、Pと共通部分を持つ。
  let S := Finset.filter (fun s => x.val ∈ s ∧ SF.sets s) SF.toSetFamily.ground.powerset
  let T := Finset.filter (fun s => x.val ∉ s ∧ SF.sets s) SF.toSetFamily.ground.powerset
  let P := equivalent_vertex SF ⟨x.val, x.property⟩
  have ha:  (∀ s : S, (s.val \ (P.image Subtype.val)) ∈ T) :=
  by
    dsimp [RS] at h1
    apply minimal_element_is_rare_lemma SF x h1

  let i : S → T := fun ss => ⟨(ss.val \ (P.image Subtype.val)), by
    exact ha ss⟩

  --iの単射性の証明
  have i_inj: ∀ s1 s2 : S, i s1 = i s2 → s1 = s2 :=
  by
    dsimp [i]
    intro s1 s2
    intro h
    simp at h
    obtain ⟨s1v,s1p⟩ := s1
    obtain ⟨s2v,s2p⟩ := s2
    have sfs1 :SF.sets (Finset.image Subtype.val (Finset.subtype (fun ss => ss ∈ SF.ground) s1v)):=
    by
      simp_all only [Subtype.coe_eta, ne_eq, RS, P]
      simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
      convert s1p.2.2
      ext y
      apply Iff.intro
      · intro a
        simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
          exists_eq_right_right]

      · intro a
        simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
          exists_eq_right_right, true_and]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := s1p
        simp_all only
        exact left a

    have :x ∈ Finset.subtype (fun ss => ss ∈ SF.ground) s1v := by
      dsimp [S] at s1p
      rw [Finset.mem_filter] at s1p
      rw [Finset.subtype]
      simp
      use x
      simp
      simp_all only [Subtype.coe_eta, ne_eq, Finset.mem_powerset, RS, P]

    have pi1:P.image Subtype.val ⊆ s1v := by
      dsimp [P]
      let equiv := equivalent_vertex_set_lemma SF x (s1v.subtype (fun ss => ss ∈ SF.ground)) sfs1 this
      simp_all only [Subtype.coe_eta, ne_eq, RS, P]
      simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
      intro y hy
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      obtain ⟨w, h_1⟩ := hy
      dsimp [equivalent_vertex] at h_1
      simp_all only [Finset.mem_filter, Finset.mem_attach, true_and]
      obtain ⟨left_4, right_2⟩ := h_1
      dsimp [vertexorder_is_preorder] at left_4
      dsimp [vertexorder] at left_4
      simp_all only [true_and]

    have xins:x ∈ Finset.subtype (fun ss => ss ∈ SF.ground) s2v := by
      dsimp [S] at s1p
      rw [Finset.mem_filter] at s2p
      rw [Finset.subtype]
      simp
      use x
      simp
      simp_all only [Subtype.coe_eta, ne_eq, Finset.mem_powerset, RS, P]

    have pi2:P.image Subtype.val ⊆ s2v := by
      dsimp [P]
      let equiv := equivalent_vertex_set_lemma SF x (s1v.subtype (fun ss => ss ∈ SF.ground)) sfs1 this
      simp_all only [Subtype.coe_eta, ne_eq, RS, P]
      simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
      obtain ⟨val, property⟩ := x
      simp_all only
      intro y hy
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      obtain ⟨w, h_1⟩ := hy
      dsimp [equivalent_vertex] at h_1
      simp_all only [Finset.mem_filter, Finset.mem_attach, true_and]
      obtain ⟨left_4, right_2⟩ := h_1
      dsimp [vertexorder_is_preorder] at left_4
      dsimp [vertexorder] at left_4
      simp_all only [true_and]

    simp at h

    have : s1v = s2v :=
    by
      ext a
      apply Iff.intro
      · intro a_1
        by_cases h1: a ∈ Finset.image Subtype.val P
        case pos =>
          have :a ∈ s2v := by
            exact pi2 h1
          exact this
        case neg =>
          have :a ∈ (s1v \ Finset.image Subtype.val P) :=
          by
            rw [Finset.mem_sdiff]
            constructor
            · exact a_1
            · exact h1
          rw [h] at this
          simp_all only [Subtype.coe_eta, ne_eq, Finset.mem_filter, Finset.mem_powerset,
            Finset.mem_subtype, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            not_exists, Finset.mem_sdiff, exists_false, not_false_eq_true, and_true]

      · intro a_1
        by_cases h1: a ∈ Finset.image Subtype.val P
        case pos =>
          have :a ∈ s1v := by
            exact pi1 h1
          exact this
        case neg =>
          have :a ∈ (s2v \ Finset.image Subtype.val P) :=
          by
            rw [Finset.mem_sdiff]
            constructor
            · exact a_1
            · exact h1
          rw [←h] at this
          rw [Finset.mem_sdiff] at this
          exact this.1
    rename_i P_1 this_1
    subst this
    simp_all only [Subtype.coe_eta, ne_eq, Finset.mem_subtype, RS, P_1, P, S]
    --ここで単射性の証明が終わり。

  --あとは、単射が存在した場合に、頂点がrareになることを証明する補題を利用して証明完了
  apply injection_rare_lemma SF x
  use i
