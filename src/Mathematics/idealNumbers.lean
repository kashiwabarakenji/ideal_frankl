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
          have v_not_in_a : v ∉ a := by
            intro h_in -- v ∈ a
            simp [f] at h
            have h_erase := Finset.erase_insert (Finset.not_mem_erase v a)
            have h_erase2 := Finset.erase_insert (Finset.not_mem_erase v b)
            -- aは、right_sideの要素である?何を使って示せる。
            have h_in_right : a ∈ right_side := by
              rw [Multiset.mem_filter]
              constructor
              · exact h_in
              · use a
                constructor
                · exact h_erase
                · exact h_in
                · exact h_erase


            --h : a cup {v}=b cup {v}
            --h_in : v ∈ a


            --exact Finset.not_mem_singleton _ h_in
            --exact Finset.not_mem_of_mem_erase h_in

          have v_not_in_b : v ∉ b := by
            intro h_in
            exact Finset.not_mem_of_mem_erase h_in

          have h_erase_a : a = (a ∪ {v}).erase v := Finset.erase_insert v_not_in_a
          have h_erase_b : b = (b ∪ {v}).erase v := Finset.erase_insert v_not_in_b
          rw [←h_erase_a, ←h_erase_b, h]

      -- 全射を示す
      have h_surjective : Function.Surjective (fun (x :Finset α) => x.erase v) :=
        by
          intro s
          use s ∪ {v}
          split
          · exact Finset.erase_insert (Finset.not_mem_erase v s)
          · refl

      -- 単射性と全射性から全単射性を得る
      apply Multiset.card_map_eq_of_bijective
      exact ⟨h_injective, h_surjective⟩

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
