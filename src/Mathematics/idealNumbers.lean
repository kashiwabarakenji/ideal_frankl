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
--set_option maxHeartbeats 500000 -- Increase the heartbeat limit
namespace Mathematics
variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

--この部分は、汎用に使えるので、後日、BasicLemmasに移動する。
--全単射があるとき、集合の要素数が等しいことを示す。
theorem finset_card_eq_card_of_bijective {α β : Type} [DecidableEq α] [Fintype α][DecidableEq β]{s : Finset α}[DecidableEq {x // x ∈ s}] {t : Finset β}
  (f : s → t) (hf : Function.Bijective f)  : s.card = t.card := by
  --have h_inj : Function.Injective f := hf.1
  have h_inj : Function.Injective f := hf.1

  have h_image : t = (s.attach).image (λ ss=> (f ss).val) := Finset.ext (by
    --simp [hf.2]
    --gaol ∃ a_2 ∈ s, f a_2 = a
    --fが全射なので、a ∈ t ならば、a = f a' となるa'が存在する。
     intro a
     constructor
     · --goal : a ∈ t → a ∈ s.image f
      intro ha
      -- ha: a ∈ t
      let surjf := hf.2
      rw [Function.Surjective] at surjf
      --surjf : ∀ (b : β), ∃ (a : α), f a = b
      let surjfa := surjf ⟨a, ha⟩
      obtain ⟨b, hb⟩ := surjfa
      --hb : f b = ⟨a, ha⟩
      --a ∈ Finset.image (fun s ↦ ↑(f s)) s.attach
      rw [Finset.mem_image]
      --goal  ∃ a_1 ∈ s.attach, ↑(f a_1) = a
      use b
      simp
      simp [hb]
     · --goal a ∈ Finset.image (fun s ↦ ↑(f s)) s.attach → a ∈ t
      intro ha
      --ha : a ∈ Finset.image (fun s ↦ ↑(f s)) s.attach
      rw [Finset.mem_image] at ha
      obtain ⟨b, _, hb2⟩ := ha
      --hb1 : b ∈ s.attach
      --hb2 : ↑(f b) = a
      --a ∈ t
      rw [←hb2]
      subst hb2
      simp_all only [Multiset.bijective_iff_map_univ_eq_univ, Finset.univ_eq_attach, Finset.attach_val,
        Finset.mem_attach, Finset.coe_mem]
    )

  calc
    s.card = s.attach.card := by rw [Finset.card_attach]
    _ = (s.attach.image (λ ss => (f ss).val)).card := by
      apply Eq.symm
      apply Finset.card_image_of_injOn
      intro x _ y _ h
      simp only [Subtype.val_inj] at h
      have : f x = f y := by
        ext
        rw [h]
      exact h_inj this
    _ = t.card := by rw [← h_image]


--theorem Finset.card_image_of_injective {α : Type u_1}  {β : Type u_2}  {f : α → β} [DecidableEq β]  (s : Finset α)  (H : Function.Injective f) :
--Finset.card (Finset.image f s) = Finset.card s

-- 言明：頂点 v を含む hyperedge 数と、v で contraction して得られた集合族の hyperedge 数が等しいことを示す

theorem degree_eq_contraction_degree {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (v : α) (hv : v ∈ F.ground) (gcard: F.ground.card ≥ 2):
  degree F v = number_of_hyperedges (IdealDeletion.contraction F v hv gcard) :=
by
  rw [IdealDeletion.contraction, degree, number_of_hyperedges]
  dsimp [all_subsets]
  simp
  --leftとrightが間違って入れ替わっているので、注意。
  let left_side := Finset.filter (fun (s :Finset α) ↦ F.sets s ∧ v ∈ s) F.ground.powerset
  let right_side := Finset.filter (fun (s :Finset α) ↦ ∃ (H:Finset α), F.sets H ∧ v ∈ H ∧ s = H.erase v) (F.ground.erase v).powerset
  have right_side_def: right_side = Finset.filter (fun (s :Finset α) ↦ ∃ (H :Finset α), F.sets H ∧ v ∈ H ∧ s = H.erase v) (F.ground.erase v).powerset := rfl
  --have left_side_def: left_side = Finset.filter (fun (s :Finset α) ↦ F.sets s ∧ v ∈ s) F.ground.powerset := rfl

  -- 左側から右側への全単射を構成
  have h_bijective : Finset.card right_side = Finset.card left_side :=
    by
      let f : {s // s ∈ right_side} → {s // s ∈ left_side} := fun s => ⟨s.val ∪ {v}, by
        -- s.val ∪ {v} が left_side に属することを証明します。
        rw [Finset.mem_filter]

        -- right_side に属していることから得られる情報を利用する
        have hs := s.property
        rw [Finset.mem_filter] at hs
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
          --have v_val_in : a.val ∈ right_side := by
          --  exact a.property
          let ap := a.property
          rw [Finset.mem_filter] at ap
          obtain ⟨Ha1,Ha2, Ha_sets, Ha3,Ha4⟩ := ap
          have ha_subset : a.val ⊆ F.ground.erase v := by
            exact Finset.mem_powerset.mp Ha1
          have v_not_in_a : v ∉ a.val := by
            rw [Finset.powerset] at Ha1
            simp [Ha4]

          let bp := b.property
          rw [Finset.mem_filter] at bp
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
          rw [Finset.mem_filter] at ss_sets
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
              rename_i α_1 _ _ _ inst_3 inst_4
              simp_all only [ge_iff_le, Finset.mem_val, Finset.mem_powerset, right_side, left_side, f, ssev]
              obtain ⟨val, property⟩ := ss
              simp_all only
              intro x hx
              simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
              obtain ⟨_, right⟩ := hx
              exact sss_subset right
            · -- right goal: ssev ⊆ F.ground.erase v
              rename_i α_1 _ _ _ inst_3 inst_4
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
          rename_i α_1 _ _ _ inst_3 inst_4
          simp [rw_rule]
          -- goal: ssev ∪ {v} = ss.val
          simpa [rw_rule] -- simpもsimpaも両方とも必要みたい。

          -- 単射性と全射性から全単射性を得る
          --fが全単射という言明をまず証明する
      have h_bijection : Function.Bijective f :=
        by
         exact ⟨h_injective, h_surjective⟩
      --fが全単射なので、right_side と left_side の要素数は等しい。
      exact finset_card_eq_card_of_bijective f h_bijection
      --これで、Finset.card right_side = Finset.card left_side が証明された。
  --congr たぶんcongrはだめ。両辺で対応してない。
  --goal Finset.card (Finset.filter (λ (s : Finset α), F.sets s ∧ v ∈ s) F.ground.powerset) = Finset.card (Finset.filter (λ (s : Finset α), ∃ (H : Finset α), F.sets H ∧ v ∈ H ∧ s = H.erase v) (F.ground.erase v).powerset)
  have r_eq: (Finset.filter (fun (s: Finset α) ↦ F.sets s ∧ v ∈ s) F.ground.powerset).card =left_side.card := by
    rfl
  rw [r_eq]

  rw [←h_bijective]

  --have l_eq :(Finset.filter (fun (s: Finset α) ↦ ∃ (H:Finset α), F.sets H ∧ v ∈ H ∧ s = H.erase v) (F.ground.erase v).powerset).card = right_side.card := by
  --  rfl
  --rw [l_eq] うまくマッチしなかった。
  --集合でなく、cardにして、置き換えた。
  have right_side_card_eq: right_side.card = Finset.card (Finset.filter (fun (s : Finset α) ↦ ∃ (H : Finset α), F.sets H ∧ v ∈ H ∧ s = H.erase v) (F.ground.erase v).powerset) := rfl
  rw [right_side_card_eq]
  congr
  --同じ式なのに全然マッチしてくれなかったが、ゴールを両辺が等しい形まで変形して、congrで簡約させてうまくいった。
