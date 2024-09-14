import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
--import Mathlib.Init.Function
import Mathlib.Init.Logic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import Ideal.IdealDeletion
import Mathlib.Data.Multiset.Basic
import LeanCopilot
--set_option maxHeartbeats 500000 -- Increase the heartbeat limit

namespace Ideal
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
            rw [Ideal.erase_insert H1 v hH3]
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
          rw [Ideal.union_erase_singleton a.val v v_not_in_a] at h_erase_eq
          rw [Ideal.union_erase_singleton b.val v v_not_in_b] at h_erase_eq
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
              --rename_i α_1 _ _ _ inst_3 inst_4
              simp_all only [ge_iff_le, Finset.mem_val, Finset.mem_powerset, right_side, left_side, f, ssev]
              obtain ⟨val, property⟩ := ss
              simp_all only
              intro x hx
              simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
              obtain ⟨_, right⟩ := hx
              exact sss_subset right
            · -- right goal: ssev ⊆ F.ground.erase v
              --rename_i α_1 _ _ _ inst_3 inst_4
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
          have rw_rule := Ideal.erase_insert' ss.val v ss_erase
          constructor
          -- goal: F.sets ssev
          --rename_i α_1 _ _ _ inst_3 inst_4
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

  -- 補題 1: Deletion後の集合族の性質
lemma deletion_property {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (v : α) (hv : v ∈ F.ground) (gcard: F.ground.card ≥ 2):
  ∀ s, (IdealDeletion.deletion F v hv gcard).sets s ↔ F.sets s∧ v ∉ s :=
by
  intro s
  constructor
  · intro hs
    rw [IdealDeletion.deletion] at hs
    simp at hs
    constructor
    exact hs.1
    exact hs.2

  · intro hs
    rw [IdealDeletion.deletion]
    simp
    exact hs

-- 補題 2: 元の集合族における次数の定義。いらないかも。
lemma degree_definition {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (v : α) :
  degree F v = Finset.card (Finset.filter (λ s => F.sets s = true ∧ v ∈ s) (Finset.powerset F.ground)) :=
by
  rw [degree]
  congr

lemma hyperedge_count_split {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (v : α) (hv : v ∈ F.ground) (gcard: F.ground.card ≥ 2):
  number_of_hyperedges F = number_of_hyperedges (IdealDeletion.deletion F v hv gcard) + degree F v :=
by
 -- まず、number_of_hyperedges の定義に基づいて、全てのハイパーエッジをカウントします
  rw [number_of_hyperedges]
  rw [number_of_hyperedges]

  -- 全ての部分集合に対するフィルタリングを行います。
  let all_sets2 := (Finset.powerset F.ground).filter F.sets

  -- このフィルタリングした集合を元に、カード（要素数）を計算します。
  --have count_all_sets : all_sets2.card = Finset.card all_sets2 := rfl

  -- 同様に、deletion後の集合族のハイパーエッジ数を計算します。
  --let deletion_sets := (Finset.powerset (F.ground.erase v)).filter (λ s => F.sets s ∧ v ∉ s)
  --以下は動いているが、使っていない。
  --have count_deletion_sets : number_of_hyperedges (IdealDeletion.deletion F v hv gcard) = deletion_sets.card :=
  --  by
  --    rw [number_of_hyperedges]
  --    congr!

  -- 次に、degreeを計算します。これは、vを含む全ての部分集合の数に対応します。
  rw [degree_definition F v]

  -- ハイパーエッジ全体の集合は、vを含むものと含まないもので分割できます。
  let sets_with_v := all_sets2.filter (λ s => v ∈ s)
  let sets_without_v := all_sets2.filter (λ s => v ∉ s)
  have sets_without_v_def: sets_without_v = all_sets2.filter (λ s => v ∉ s) := rfl


  -- この分割が正確であることを確認します。
  have partition : all_sets2 = sets_with_v ∪ sets_without_v := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_powerset, Finset.mem_erase, and_iff_right_iff_imp, or_iff_not_imp_left]
    constructor
    -- s ∈ all_sets の場合を考える
    intro hs
    by_cases h : v ∈ s
    -- v ∈ s の場合、s ∈ sets_with_v
    case pos =>
      simp [sets_with_v, *]
    -- v ∉ s の場合、s ∈ sets_without_v
    case neg =>
      simp [sets_without_v, *]

    -- s ∈ sets_with_v ∪ sets_without_v の場合を考える
    intro hs
    -- hs : s ∈ sets_with_v ∨ s ∈ sets_without_v
    by_cases hss : s ∈ sets_with_v
    case pos h_with_v =>
      --goal s ∈ sets_with_v
      dsimp [sets_with_v] at hss
      rw [Finset.mem_filter] at hss
      exact hss.1
    case neg h_without_v =>
      have hsss:= hs hss
      dsimp [sets_without_v] at hsss
      rw [Finset.mem_filter] at hsss
      exact hsss.1

  -- 最後に、全ての部分集合のカード（要素数）が、分割された集合のカード（要素数）の合計と等しいことを示します。
  --goal Finset.card all_sets = Finset.card sets_with_v + Finset.card sets_without_v
  --simp_all
  have partition_card : all_sets2.card = (sets_with_v ∪ sets_without_v).card := by
    rw [partition]
  have term1: (Finset.filter F.sets F.ground.powerset).card = all_sets2.card := rfl

  have term2: (Finset.filter (λ (s : Finset α)=> F.sets s ∧ v ∈ s) (Finset.powerset F.ground)).card = sets_with_v.card := by
    simp [sets_with_v]
    simp [all_sets2]
    simp [Finset.filter]
    apply congr_arg
    apply Multiset.filter_congr
    tauto
  have term3: (Finset.filter (λ (s : Finset α)=> F.sets s = true ∧ v ∉ s) (Finset.powerset F.ground)).card = sets_without_v.card :=
    by
      simp [sets_without_v]
      simp [all_sets2]
      simp [Finset.filter]
      apply congr_arg
      apply Multiset.filter_congr
      tauto

  have term_eq: Finset.filter ((F ∖ v) hv gcard).sets ((F ∖ v) hv gcard).ground.powerset = sets_without_v := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset, IdealDeletion.deletion, and_iff_right_iff_imp]
    constructor
    · intro hs --a.mp.left
      dsimp [sets_without_v]
      dsimp [all_sets2]
      rw [Finset.mem_filter]
      simp [Finset.filter]
      constructor
      constructor
      exact F.inc_ground s hs.2.1
      exacts [hs.2.1, hs.2.2]
    · intro h -- a.mp.right goal: s ⊆ F.ground.erase v ∧ F.sets s ∧ v ∉ s
      --unfold sets_without_v at h
      rw [sets_without_v_def] at h
      dsimp [all_sets2] at h
      rw [Finset.mem_filter] at h
      simp [Finset.filter] at h
      constructor
      apply Finset.subset_erase.mpr
      constructor
      exact h.1.1
      exact h.2

      --goal F.sets s ∧ v ∉ s
      constructor
      exact h.1.2
      exact h.2

  rw [term1]
  rw [partition_card]
  dsimp [sets_with_v]
  dsimp [sets_without_v]
  dsimp [all_sets2]
  rw [Finset.card_union_of_disjoint]
  rw [term_eq]
  simp
  rw [term2]
  --rw [add_comm sets_with_v.card sets_without_v.card]
  rw [←term2]--add_commとの順番で適用できなくなる。
  rw [←term3]
  rw [add_comm]

  have disj: Disjoint (Finset.filter (fun s ↦ v ∈ s) (Finset.filter F.sets F.ground.powerset)) (Finset.filter (fun s ↦ v ∉ s) (Finset.filter F.sets F.ground.powerset)) :=
    by
      -- sets_with_v と sets_without_v の交わりが空集合であることを示す必要があります。
      apply Finset.disjoint_filter.2
      simp

  exact disj
  --原因不明でexact disjができなかったが、原因不明でできるようになった。

theorem hyperedge_count_deletion_contraction {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2)
  [DecidablePred F.sets] (hx_hyperedge : F.sets (F.ground \ {x})) :
  number_of_hyperedges F.toSetFamily =
  number_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily +
  number_of_hyperedges (IdealDeletion.contraction F.toSetFamily x hx gcard) :=
by
--theorem degree_eq_contraction_degree {α : Type} [DecidableEq α] [Fintype α]
--F : SetFamily α) (v : α) (hv : v ∈ F.ground) (gcard: F.ground.card ≥ 2):
--  degree F v = number_of_hyperedges (IdealDeletion.contraction F v hv gcard) :=
--hyperedge_count_split {α : Type} [DecidableEq α] [Fintype α]
--  (F : SetFamily α) (v : α) (hv : v ∈ F.ground) (gcard: F.ground.card ≥ 2):
--  number_of_hyperedges F = number_of_hyperedges (IdealDeletion.deletion F v hv gcard) + degree F v
-- calcで計算できるかも。
  --#check hyperedge_count_split F.toSetFamily x hx gcard
  have sub1: number_of_hyperedges F.toSetFamily = number_of_hyperedges ((F.toSetFamily ∖ x) hx gcard) + degree F.toSetFamily x := by
    rw [←hyperedge_count_split F.toSetFamily x hx gcard]
    congr

  have sub2: (IdealDeletion.idealdeletion F x hx gcard).toSetFamily = (IdealDeletion.deletion F.toSetFamily x hx gcard) := by
    dsimp [IdealDeletion.idealdeletion]
    dsimp [IdealDeletion.deletion]
    congr
    --rename_i α_1 inst inst_1 inst_2 inst_3 inst_4 inst_5
    ext x_1 : 2
    simp_all only [or_iff_left_iff_imp, Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]
    intro a
    subst a
    convert hx_hyperedge
    ext1 a
    simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
    apply Iff.intro
    · intro a_1
      simp_all only [not_false_eq_true, and_self]
    · intro a_1
      simp_all only [not_false_eq_true, and_self]

  calc
    number_of_hyperedges F.toSetFamily
    _ = number_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard) + degree F.toSetFamily x := by rw [sub1]
    _ = number_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily + degree F.toSetFamily x := by rw [←sub2]
    _ = number_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily + number_of_hyperedges (IdealDeletion.contraction F.toSetFamily x hx gcard) := by
      rw [degree_eq_contraction_degree F.toSetFamily x hx gcard]

theorem hyperedge_count_deletion_contraction_none {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2)
  [DecidablePred F.sets] (hx_hyperedge_not : ¬ F.sets (F.ground \ {x})) :
  number_of_hyperedges F.toSetFamily + 1=
  number_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily  +
  number_of_hyperedges (IdealDeletion.contraction F.toSetFamily x hx gcard) :=
  by
    have sub1: number_of_hyperedges F.toSetFamily = number_of_hyperedges ((F.toSetFamily ∖ x) hx gcard) + degree F.toSetFamily x := by
      rw [←hyperedge_count_split F.toSetFamily x hx gcard]
      congr

    have sub2:∀(s : Finset α),(IdealDeletion.idealdeletion F x hx gcard).toSetFamily.sets s ↔ (IdealDeletion.deletion F.toSetFamily x hx gcard).sets s  ∨ (s = F.ground \ {x}):= by
      dsimp [IdealDeletion.idealdeletion]
      dsimp [IdealDeletion.deletion]
      intro s
      --congr
      apply Iff.intro
      · intro a
        cases a with
        | inl h => simp_all only [not_false_eq_true, and_self, true_or]
        | inr h_1 =>
          subst h_1
          simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]
          apply Or.inr
          ext1 a
          simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
          apply Iff.intro
          · intro a_1
            simp_all only [not_false_eq_true, and_self]
          · intro a_1
            simp_all only [not_false_eq_true, and_self]
      · intro a
        cases a with
        | inl h => simp_all only [not_false_eq_true, and_self, true_or]
        | inr h_1 =>
          subst h_1
          simp_all only [Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false, and_false, not_false_eq_true,
            and_true, false_or]
          ext1 a
          simp_all only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_erase, ne_eq]
          apply Iff.intro
          · intro a_1
            simp_all only [not_false_eq_true, and_self]
          · intro a_1
            simp_all only [not_false_eq_true, and_self]

    --なくすと影響がある？
    have : ∀(s : Finset α) (a : α), a ∉ s → (insert a s).card = s.card + 1 := by
      intro s a h
      exact Finset.card_insert_of_not_mem h


    have card_insert_of_not_mem_set: ∀(s : Finset (Finset α)) (a : Finset α), a ∉ s → (insert a s).card = s.card + 1 := by
      intro s a h
      exact Finset.card_insert_of_not_mem h

    --#check (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) (F.ground.erase x).powerset)
    --#check (Finset.filter (fun (s:Finset α) ↦ F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) (F.ground.erase x).powerset)
    have hx_not: (F.ground \ {x}) ∉ Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) (F.ground.erase x).powerset:=
      by
        rw [←Finset.sdiff_singleton_eq_erase]
        simp_all only [not_false_eq_true, Finset.card_insert_of_not_mem, implies_true, Finset.mem_filter,
          Finset.mem_powerset, Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false, and_false, and_true]

    let sub3 := card_insert_of_not_mem_set (Finset.filter (fun (s:Finset α) ↦ F.sets s ∧ x ∉ s) (F.ground.erase x).powerset)  (F.ground \ {x}) hx_not

    have sub5:  (insert (F.ground \ {x}) (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) (F.ground.erase x).powerset)) = (Finset.filter (fun (s:Finset α) ↦ F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) (F.ground.erase x).powerset) := by
      ext1 a
      simp_all only [Finset.mem_insert, Finset.mem_filter, Finset.mem_powerset, Finset.mem_sdiff, Finset.mem_singleton]
      apply Iff.intro
      intro a_1
      simp_all only [not_false_eq_true, Finset.card_insert_of_not_mem, implies_true]
      cases a_1 with
      | inl h =>
        subst h
        simp_all only [Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false, and_false, not_false_eq_true,
          and_true, false_or]
        apply And.intro
        · rw [Finset.sdiff_singleton_eq_erase]
        · rw [Finset.sdiff_singleton_eq_erase]
      | inr h_1 => simp_all only [not_false_eq_true, and_self, true_or]
      intro a_1
      simp_all only [not_false_eq_true, Finset.card_insert_of_not_mem, implies_true, true_and]
      obtain ⟨left, right⟩ := a_1
      cases right with
      | inl h => simp_all only [not_false_eq_true, and_self, or_true]
      | inr h_1 =>
        subst h_1
        simp_all only [Finset.Subset.refl, Finset.mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]
        apply Or.inl
        ext1 a
        simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
        apply Iff.intro
        · intro a_1
          simp_all only [not_false_eq_true, and_self]
        · intro a_1
          simp_all only [not_false_eq_true, and_self]

    have sub4: number_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard) + 1 =  (number_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily) :=
      by
        dsimp [number_of_hyperedges]
        dsimp [IdealDeletion.deletion]
        dsimp [IdealDeletion.idealdeletion]
        dsimp [IdealDeletion.deletion] at sub2
        dsimp [IdealDeletion.idealdeletion] at sub2
        simp_all
        rw [Finset.sdiff_singleton_eq_erase]
        rw [Finset.sdiff_singleton_eq_erase] at sub3
        simp_all
        rw [Finset.sdiff_singleton_eq_erase]
        rw [Finset.sdiff_singleton_eq_erase] at sub5

        rw [sub5] at sub3
        rw [sub3]
        simp_all
        congr

        -- goal (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s) (F.ground.erase x).powerset).card + 1 =
        -- (Finset.filter (fun s ↦ F.sets s ∧ x ∉ s ∨ s = F.ground.erase x) (F.ground.erase x).powerset).card
        --hx_hyperedge_not : ¬F.sets (F.ground \ {x})
        --exact Finset.card_insert_of_not_mem hyperedge_notをつかうとよい。

    calc
        number_of_hyperedges F.toSetFamily + 1
    _ = number_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard) + degree F.toSetFamily x + 1 := by rw [sub1]
    _= number_of_hyperedges (IdealDeletion.deletion F.toSetFamily x hx gcard) + 1 + degree F.toSetFamily x := by ring
    _ = number_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily + degree F.toSetFamily x := by rw [sub4]
    _ = number_of_hyperedges (IdealDeletion.idealdeletion F x hx gcard).toSetFamily + number_of_hyperedges (IdealDeletion.contraction F.toSetFamily x hx gcard) := by
      rw [degree_eq_contraction_degree F.toSetFamily x hx gcard]




end Ideal