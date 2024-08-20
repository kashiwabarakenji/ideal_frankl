import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Mathlib.Init.Function
import Mathlib.Init.Logic
import Mathematics.BasicDefinitions
import Mathematics.BasicLemmas
import Mathematics.IdealDeletion
import Mathlib.Data.Multiset.Basic
import LeanCopilot

namespace Mathematics
variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

-- 言明：頂点 v を含む hyperedge 数と、v で contraction して得られた集合族の hyperedge 数が等しいことを示す
theorem degree_eq_contraction_degree {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (v : α) (hv : v ∈ F.ground) (gcard: F.ground.card ≥ 2):
  degree F v = number_of_hyperedges (IdealDeletion.contraction F v hv gcard) :=
by
  rw [IdealDeletion.contraction, degree, number_of_hyperedges]
  dsimp [Finset.filter, all_subsets]
  simp

  let left_side := Multiset.filter (fun s ↦ F.sets s ∧ v ∈ s) F.ground.powerset.val
  let right_side := Multiset.filter (fun s ↦ ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v) (F.ground.erase v).powerset.val
  have right_side_def: right_side = Multiset.filter (fun s ↦ ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v) (F.ground.erase v).powerset.val := rfl
  have left_side_def: left_side = Multiset.filter (fun s ↦ F.sets s ∧ v ∈ s) F.ground.powerset.val := rfl

  -- 左側から右側への全単射を構成
  have h_bijective : Multiset.card right_side = Multiset.card left_side :=
    by
      let f : {s // s ∈ right_side} → {s // s ∈ left_side} := fun s => ⟨s.val ∪ {v}, by
        -- s.val ∪ {v} が left_side に属することを証明します。
        rw [Multiset.mem_filter]

        -- right_side に属していることから得られる情報を利用する
        have hs := s.property
        rw [Multiset.mem_filter] at hs
        rcases hs with ⟨hs1, hs2⟩

        constructor
        -- s.val ∪ {v} ⊆ F.ground を示す部分
        · have sfge: s.val ⊆ F.ground.erase v := Finset.mem_powerset.mp hs1
          have fgsubset: F.ground.erase v ⊆ F.ground := Finset.erase_subset v F.ground
          have sfg: s.val ⊆ F.ground := sfge.trans fgsubset
          have svfg: s.val ∪ {v} ⊆ F.ground :=
            by
              intro ss hss
              cases Finset.mem_union.mp hss with
              | inl hss => exact sfg hss
              | inr hss =>
                simp at hss
                rw [hss]
                exact hv
          exact Finset.mem_powerset.mpr svfg

        constructor
        · --goal F.sets (s ∪ {v})
          --hs2 : ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v
          rcases hs2 with ⟨H1, H2, hH3, hh4⟩
          --obtain ⟨H, H_sets, hHH, _⟩ := hs2

          have Fssv: F.sets (s.val ∪ {v}) := by
            rw [hh4]
            rw [Mathematics.erase_insert H1 v hH3]
            exact H2
          exact Fssv

        · --goal v ∈ s ∪ {v}
          -- v ∈ ↑s ∪ {v}
          simp⟩


      -- 単射を示す
      have h_injective : Function.Injective f :=
        by
          intros a b h
          have v_val_in : a.val ∈ right_side := by
            exact a.property
          let ap := a.property
          rw [Multiset.mem_filter] at ap
          obtain ⟨Ha1,Ha2, Ha_sets, Ha3,Ha4⟩ := ap
          have ha_subset : a.val ⊆ F.ground.erase v := by
            exact Finset.mem_powerset.mp Ha1
          have v_not_in_a : v ∉ a.val := by
            rw [Finset.powerset] at Ha1
            simp [Ha4]

          let bp := b.property
          rw [Multiset.mem_filter] at bp
          obtain ⟨Hb1,Hb2, Hb_sets, Hb3,Hb4⟩ := bp
          have hb_subset : b.val ⊆ F.ground.erase v := by
            exact Finset.mem_powerset.mp Hb1
          have v_not_in_b : v ∉ b.val := by
            rw [Finset.powerset] at Hb1
            simp [Hb4]
          -- h: f a = f b
          -- f: {s // s ∈ right_side} → {s // s ∈ left_side} := fun s => ⟨s.val ∪ {v}, _⟩
          -- f a = f b から a = b を示す
          have h_eq := congr_arg (λ s => s.val) h
          have h_eq2 : a.val ∪ {v} = b.val ∪ {v} := by
            exact h_eq
          have h_erase_eq : (a.val ∪ {v}).erase v = (b.val ∪ {v}).erase v := by
             rw [h_eq2]
          rw [Mathematics.union_erase_singleton a.val v v_not_in_a] at h_erase_eq
          rw [Mathematics.union_erase_singleton b.val v v_not_in_b] at h_erase_eq
          have h_eq3 : a.val = b.val := by
            simp [h_erase_eq]
          exact Subtype.eq h_eq3

      -- 全射を示す
      have h_surjective : Function.Surjective f :=
        by
          intro ss
          let ssev := ss.val.erase v
          have ssev_def: ssev = ss.val.erase v := by
            rfl

          have ss_sets := ss.property
          rw [Multiset.mem_filter] at ss_sets
          obtain ⟨sss_sets, ss_v, ss_erase⟩ := ss_sets
          have sss_subset: ss.val ⊆ F.ground := by
            exact Finset.mem_powerset.mp sss_sets
          have s_subset : ssev ∪ {v} ⊆ F.ground := by
            simp [ssev_def]
            rw [Finset.union_subset_iff]
            constructor

            · -- left goal: ssev ⊆ F.ground
             have ssss_subset := Finset.erase_subset v ss.val --  (↑ss).erase v ⊆ ↑ss
             -- sss_subset : ↑ss ⊆ F.ground
             exact Finset.Subset.trans ssss_subset sss_subset
            · -- right goal: {v} ⊆ F.ground
              simp
              exact hv

          have s_in_right_side : ssev ∈ right_side := by
            rw [right_side_def]
            simp
            constructor
            · -- left goal: F.sets ssev
              rename_i α_1 inst inst_1 inst_2 inst_3 inst_4
              simp_all only [ge_iff_le, Finset.mem_val, Finset.mem_powerset, right_side, left_side, f, ssev]
              obtain ⟨val, property⟩ := ss
              simp_all only
              intro x hx
              simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
              obtain ⟨left, right⟩ := hx
              exact sss_subset right
            · -- right goal: ssev ⊆ F.ground.erase v
              rename_i α_1 inst inst_1 inst_2 inst_3 inst_4
              simp_all only [ge_iff_le, Finset.mem_val, Finset.mem_powerset, right_side, left_side, f, ssev]
              obtain ⟨val, property⟩ := ss
              simp_all only
              apply Exists.intro
              · apply And.intro
                on_goal 2 => {
                  apply And.intro
                  on_goal 2 => {apply Eq.refl
                  }
                  · simp_all only
                }
                · simp_all only
          --全射性のgoal ∃ a, f a = ss
          let element_in_right_side : {s // s ∈ right_side} :=
              ⟨ssev, s_in_right_side⟩
          dsimp [f]
          simp_all
          use element_in_right_side
          simp only [ssev, Finset.mem_erase]
          have rw_rule := Mathematics.erase_insert' ss.val v ss_erase
          constructor
          -- goal: F.sets ssev
          rename_i α_1 inst inst_1 inst_2 inst_3 inst_4
          simp [rw_rule]
          -- goal: ssev ∪ {v} = ss.val
          simpa [rw_rule]

      -- 単射性と全射性から全単射性を得る
      --fが全単射という言明をまず証明する
      have h_bijective : Function.Bijective f :=
        by
          exact ⟨h_injective, h_surjective⟩
      --fが全単射なので、right_side と left_side の要素数は等しい。
      exact Finset.card_eq_of_bijective h_bijective



  rw [h_bijective]
  refl

-- 言明：頂点 v を含む hyperedge 数と、v で contraction して得られた集合族の hyperedge 数が等しいことを示す
theorem degree_eq_contraction_degree2 {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (v : α) (hv : v ∈ F.ground) (gcard: F.ground.card ≥ 2):
  degree F v = number_of_hyperedges (IdealDeletion.contraction F v hv gcard) :=
by
  rw [IdealDeletion.contraction, degree, number_of_hyperedges]
  dsimp [Finset.filter, all_subsets]
  simp
  let left_side := (Multiset.filter (fun s ↦ F.sets s ∧ v ∈ s) F.ground.powerset.val)
  let right_side := (Multiset.filter (fun s ↦ F.sets s ∧ v ∈ s) (F.ground.erase v).powerset.val)
  --集合として等しいことを示すのではなく、大きさが等しいことを示す。
  --そのために全単射を作る。
  -- 全単射を構成
  let f : (Multiset (Finset α)) → (Multiset (Finset α)) := fun s =>
    Multiset.map (fun (x : Finset α) => x ∪ {v}) s

  -- 左側から右側への対応関係
  have h_injective : Function.Injective (fun (x : Finset α) => x ∪ {v}) :=
    by
      intros a b h
      have v_not_in_a : v ∉ a := by
        intro h_in
        have h' := Finset.mem_of_mem_insert_of_ne h_in (ne_of_eq_of_ne rfl (Finset.not_mem_erase v (a ∪ {v})))
        exact Finset.not_mem_erase v a h'

      have v_not_in_b : v ∉ b := by
        intro h_in
        have h' := Finset.mem_of_mem_insert_of_ne h_in (ne_of_eq_of_ne rfl (Finset.not_mem_erase v (b ∪ {v})))
        exact Finset.not_mem_erase v b h'

      have h_erase_a : a = (a ∪ {v}).erase v := Finset.erase_insert v_not_in_a
      have h_erase_b : b = (b ∪ {v}).erase v := Finset.erase_insert v_not_in_b
      rw [←h_erase_a, ←h_erase_b, h]


  have h_surjective : Function.Surjective (fun x => x.erase v) :=
    by
      intro s
      use (s ∪ {v}).erase v
      constructor
      · exact Finset.erase_insert v s (Finset.not_mem_erase v s)
      · exact Finset.erase_insert v s (Finset.not_mem_erase v s)

  -- 2つの Multiset が同じ大きさを持つことを証明
  have h_bijective : left_side.card = right_side.card :=
    by
      apply Multiset.card_map_eq_of_bijective
      exact ⟨h_injective, h_surjective⟩

  rw [h_bijective]
