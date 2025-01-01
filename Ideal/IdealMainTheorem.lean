--Ideal集合族が平均abundantにならないことの証明。IdealMain.leanのほうは、各Fin n上のIdeal集合族に対して、平均abundantにならないことを示した。
--ここでは、一般のalpha上のIdeal集合族に対して、平均abundantにならないことを示した。
--alpha上のIdeal集合族をFin n上のIdeal集合族に埋め込む関数を定義したが、大きい方から小さい方への埋め込みは、思いのほか大変だった。
--数学的には、hyperedgeの数も、hyperedgeの大きさの和も埋め込みで変化がないことは自明だが、Leanで証明するとかなり大変だった。

import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
--import Mathlib.Data.Finset.Union
--import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import Ideal.IdealDeletion
import Ideal.IdealRare
import Ideal.IdealSum
import Ideal.IdealNumbers
import Ideal.IdealDegreeOne
import Ideal.IdealFin
import Ideal.IdealMain
import Ideal.IdealDegOneMain
import LeanCopilot
set_option maxHeartbeats 500000

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α]

--Finに埋め込んでもhyperedgeの数が変わらないことの証明。数学的には自明だが、leanで証明すると大変だった。fin_total_eqとして、和が変わらないことも示す必要あり。
lemma fin_number_eq (F: IdealFamily α)(h : F.ground.card ≥ 2) (hn: Fintype.card F.ground = F.ground.card): number_of_hyperedges (toIdealFinFamily F F.ground.card hn).toSetFamily = number_of_hyperedges F.toSetFamily := by
    let n := F.ground.card
    let pall := P_all n h
    dsimp [P] at pall
    have hn2: (toIdealFinFamily F n hn).ground.card = n := by
      simp_all only [toIdealFinFamily, hn]
      let equal :=  equal_card_fin_ideal_family F hn
      --#check equal
      have equal2: Fintype.card { x // x ∈ (toIdealFinFamily F n hn).ground } = (toIdealFinFamily F n hn).ground.card := by
        exact Fintype.card_coe (toIdealFinFamily F n hn).ground
      simp_all only [n, equal]
      rfl

    let embedding := (Fintype.equivFinOfCardEq hn).toFun
    have hf: Function.Injective embedding := by
      simp_all only [embedding]
      exact (Fintype.equivFinOfCardEq hn).injective

    let GSet := (toIdealFinFamily F n hn).ground.powerset.filter (toIdealFinFamily F n hn).toSetFamily.sets
    let FSet: Finset (Finset α)  := F.ground.powerset.filter (λ S => F.toSetFamily.sets S)
    let projectToGround (x: α) (hx: x ∈ F.ground) : { x:α  // x ∈ F.ground } := ⟨x, hx⟩
    haveI : DecidablePred (λ x => x ∈ F.ground) := inferInstance
    let projectFSetToGround (S : Finset (Finset α)) : Finset (Finset { x : α // x ∈ F.ground }) :=
      S.image (λ s => Finset.filter (λ y => ∃ (x : α) (hx : x ∈ F.ground), projectToGround x hx = y ∧ x ∈ s) (Finset.univ))
    let FSet2:Finset (Finset { x // x ∈ F.ground }) := projectFSetToGround FSet


    --#check @same_cardinality ({x // x ∈ F.ground}) (Fin n)  _ _ FSet2 GSet
    have hFG : ∀ (T : Finset (Fin n)), (toIdealFinFamily F n hn).sets T ↔ ∃ (S : Finset { x // x ∈ F.ground }), F.toSetFamily.sets (S.map (Function.Embedding.subtype _)) ∧ T = S.image embedding := by

      intro T
      simp only [toIdealFinFamily]
      simp only [embedding]
      simp only [ge_iff_le, n]
      apply Iff.intro
      · intro a
        let ⟨S, hS⟩ := a
        obtain ⟨h1, h2⟩ := hS
        cases h2
        use S
        simp_all only [and_true]
        convert h1
        ext x a : 2
        simp_all only [Finset.mem_map, Function.Embedding.coe_subtype, Finset.mem_image]--

      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left_1, right_1⟩ := h
        subst right_1
        have left_2 := left_1
        simp_all only
        convert left_2
        simp_all only [iff_true]
        use w
        simp_all only [Equiv.toFun_as_coe, and_true]
        have left_2 := left_2
        simp_all only
        rw [Finset.image]
        simp only [Multiset.toFinset_map]
        simp_all only [Finset.val_toFinset]
        convert left_2
        ext ⟨x, hx⟩
        simp_all only [Finset.mem_image,Finset.mem_map, Function.Embedding.coe_subtype]--

    --補題として独立させたい。
    have hFG2: ∀ (T : Finset (Fin n)), T ∈ GSet ↔ ∃ S ∈ FSet2, T = Finset.image embedding S:= by
      dsimp [FSet2, projectFSetToGround]
      dsimp[projectToGround]
      dsimp [FSet,GSet]
      simp
      -- goal: ∀ (T : Finset (Fin n)),  T ⊆ (toIdealFinFamily F n hn).ground ∧ (toIdealFinFamily F n hn).sets T ↔ ∃ a, (a ⊆ F.ground ∧ F.sets a) ∧ T = Finset.image embedding (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ a) F.ground.attach)
      intro T
      simp_all only [toIdealFinFamily]
      simp_all only [ n, embedding]
      obtain ⟨left, right⟩ := pall
      --simp_all only [ n]
      apply Iff.intro
      · intro a
        let ⟨_, hS⟩ := a
        obtain ⟨h1, h2⟩ := hS
        cases h2
        simp_all only [Equiv.toFun_as_coe]
        --goal ∃ S_1,  F.sets (Finset.map (Function.Embedding.subtype fun x => x ∈ F.ground) S_1) ∧ Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S_1
        rename_i right_1
        subst right_1
        obtain ⟨left_2, right_1⟩ := a
        obtain ⟨w, h⟩ := right_1
        obtain ⟨left_3, right_1⟩ := h
        simp_all only
        -- goal ∃ a,  (a ⊆ F.ground ∧ F.sets a) ∧Finset.image (⇑(Fintype.equivFinOfCardEq hn)) w =Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ a) F.ground.attach)
        use w.map (Function.Embedding.subtype _)
        simp_all only [and_true, Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right, exists_eq_right]--
        apply And.intro
        · intro x hx
          simp_all only [Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right, exists_eq_right]--
          obtain ⟨w_1, _⟩ := hx
          simp_all only
        · ext1 a
          simp_all only [Finset.mem_image, Subtype.exists, Finset.mem_filter, Finset.mem_attach, true_and,Subtype.mk.injEq,exists_and_left]--
          apply Iff.intro
          · intro a_1
            simp_all only [ge_iff_le, exists_true_left, n]
          /-
          · intro a_1
            obtain ⟨w_1, h⟩ := a_1
            obtain ⟨w_2, h⟩ := h
            obtain ⟨left_4, right_2⟩ := h
            subst right_2
            simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop, exists_eq_right_right, and_true]--
            apply Exists.intro
            · apply And.intro
              · apply And.intro
                on_goal 2 => {rfl
                }
                · simp_all only
              · simp_all only
                search_proof
              · simp_all only [exists_const]
          -/
          · intro a_1
            obtain ⟨w_1, h⟩ := a_1
            obtain ⟨left_4, right_2⟩ := h
            --obtain ⟨w_2, h⟩ := left_4
            obtain ⟨w_3, h_1⟩ := right_2
            --obtain ⟨left_4, right_2⟩ := h
            --obtain ⟨_, right_3⟩ := left_4
            --obtain ⟨w_4, h⟩ := right_2
            --subst right_3 h_1
            subst h_1
            simp_all only [ge_iff_le, exists_true_left, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq,
              exists_and_right, exists_eq_right, exists_const, n]
            --simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_and_right, exists_eq_right, exists_const]
      · --(∃ a,    (a ⊆ F.ground ∧ F.sets a) ∧ T =Finset.image (⇑(Fintype.equivFinOfCardEq hn))(Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ a) F.ground.attach)) → T ⊆ (F.toFinFamily F.ground.card hn).ground ∧ ∃ S, F.sets (Finset.map (Function.Embedding.subtype fun x => x ∈ F.ground) S) ∧ T = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S
        --simp_all
        intro a
        obtain ⟨w, ha⟩ := a
        --goal { val := w, nodup := h } ⊆ F.ground → F.sets { val := w, nodup := h } → T = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ { val := w, nodup := h }) F.ground.attach) → Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ { val := w, nodup := h }) F.ground.attach) ⊆ (F.toFinFamily F.ground.card hn).ground ∧ ∃ S, F.sets (Finset.map (Function.Embedding.subtype fun x => x ∈ F.ground) S) ∧ Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ { val := w, nodup := h }) F.ground.attach) = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S
        simp_all
        constructor
        · --subst d
          intro _
          simp_all
          intro _
          intro _
          intro _
          intro e
          subst e
          --goal  (Fintype.equivFinOfCardEq hn) ⟨f, ⋯⟩ ∈ (F.toFinFamily F.ground.card hn).ground
          --#check Fintype.equivFinOfCardEq hn  -- { x // x ∈ F.ground } ≃ Fin n
          --#check (Fintype.equivFinOfCardEq hn) ⟨f, _⟩
          have univ_eq:(F.toFinFamily F.ground.card hn).ground = Finset.univ:= by
            have hn3: (F.toFinFamily F.ground.card hn).ground.card = Fintype.card (Fin F.ground.card) := by
              simp_all only [Fintype.card_fin]
            exact (Finset.card_eq_iff_eq_univ (F.toFinFamily F.ground.card hn).ground).mp hn3
          simp_all only [Finset.card_univ, Fintype.card_fin, Finset.mem_univ]
        · --goal ∃ S, F.sets (Finset.map (Function.Embedding.subtype fun x => x ∈ F.ground) S)
          -- ∧ Finset.image (⇑(Fintype.equivFinOfCardEq hn))  (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ w) F.ground.attach) = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S
          --expected Finset { x // x ∈ F.ground } -- w : Multiset alpha ha : w.Nodup
          have ha: w ⊆ F.ground := by  --使ってない。
            intro x
            intro hx
            obtain ⟨left_1, right_1⟩ := ha
            obtain ⟨left_1, _⟩ := left_1
            subst right_1
            exact left_1 hx
          use F.ground.attach.filter (fun x => x.1 ∈ w)
          rename_i ha_1
          simp_all only [true_and]
          obtain ⟨left_1, right_1⟩ := ha_1
          subst right_1
          apply And.intro
          · --goal F.sets (Finset.map (Function.Embedding.subtype fun x => x ∈ F.ground) (Finset.filter (fun x => ↑x ∈ w) F.ground.attach))
            --#check F.sets
            let S := Finset.map (Function.Embedding.subtype (λ x => x ∈ F.ground)) (Finset.filter (λ x=> ↑x ∈ w) F.ground.attach)
            -- `S` は `w` の部分集合として表されることを確認する
            have hS : S ⊆ w := by
              intro x hx
              simp_all only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach,Function.Embedding.coe_subtype, Subtype.exists,  exists_prop, exists_eq_right_right, S]--
            by_cases hc : S = F.ground
            case pos =>
              -- `S = F.ground` の場合
              simp_all only [S]
              convert left_1
              exact hS.antisymm ha
            case neg =>
              -- `S ≠ F.ground` の場合
              have hS : S ⊆ w := by
                intro x hx
                simp_all only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
                  Function.Embedding.coe_subtype, Subtype.exists, exists_and_left, exists_prop,exists_eq_right_right, S]--
              -- down_closed の性質を適用
              simp_all only [S]
              convert left_1
              ext1 a
              simp_all only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
                Function.Embedding.coe_subtype, Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right,and_iff_left_iff_imp]--
              intro a_1
              exact ha a_1

          · --goal Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ w) F.ground.attach) = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun x => ↑x ∈ w) F.ground.attach)
            simp_all only [n]
            /-
            ext1 a
            simp_all only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
              Subtype.mk.injEq, exists_prop, exists_and_left]
            apply Iff.intro
            · intro a_1
              obtain ⟨w_1, h⟩ := a_1
              obtain ⟨left_2, right_1⟩ := h
              obtain ⟨w_2, h⟩ := left_2
              obtain ⟨w_3, h_1⟩ := right_1
              obtain ⟨left_2, right_1⟩ := h
              obtain ⟨_, right_2⟩ := left_2
              subst h_1 right_2
              simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop, exists_eq_right_right,
                and_self]
            · intro a_1
              obtain ⟨w_1, h⟩ := a_1
              obtain ⟨left_2, right_1⟩ := h
              obtain ⟨w_2, h⟩ := right_1
              subst h
              simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop, exists_eq_right_right,
                and_true]
              use w_1
            -/

    have FG_eq: FSet2.card = GSet.card:= by
      apply same_cardinality FSet2 GSet embedding hf hFG2

    dsimp [FSet2, GSet] at FG_eq
    dsimp [projectFSetToGround] at FG_eq
    dsimp [projectToGround] at FG_eq
    dsimp [number_of_hyperedges, normalized_degree_sum]
    symm
    rw [←FG_eq]
    dsimp [FSet]

    -- 写像 i の定義
    let i := λ (s : Finset α) (_ : s ∈ Finset.filter F.sets F.ground.powerset) =>
        Finset.filter (λ y => ∃ x, ∃ (hx: x ∈ F.ground), ⟨x, hx⟩ = y ∧ x ∈ s) F.ground.attach

    -- 写像 i が定義域から値域に写ることの証明
    have hi : ∀ (s : Finset α) (hs : s ∈ Finset.filter F.sets F.ground.powerset),
      i s hs ∈ Finset.image (λ t => Finset.filter (λ y => ∃ x, ∃ (hx : x ∈ F.ground), ⟨x, hx⟩ = y ∧ x ∈ t) F.ground.attach) (Finset.filter F.sets F.ground.powerset) :=
      by
        intros s hs
        apply Finset.mem_image_of_mem
        exact hs

    -- 単射性の証明
    have inj : ∀ (a₁ : Finset α) (ha₁ : a₁ ∈ Finset.filter F.sets F.ground.powerset) (a₂ : Finset α)
  (ha₂ : a₂ ∈ Finset.filter F.sets F.ground.powerset), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂  := by
  --∀ (a₁ a₂ : Finset α) (ha₁ : a₁ ∈ Finset.filter F.sets F.ground.powerset)
  --     (ha₂ : a₂ ∈ Finset.filter F.sets F.ground.powerset), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ := by
      intros a1 ha1 a2 ha2 h_eq

      -- Finset の等式を示すために Finset.ext を適用
      apply Finset.ext

      -- 任意の要素 x に対して、a1 に含まれる ↔ a2 に含まれることを示す
      intro x
      constructor

      -- a1 ⊆ a2 を示す部分
      · -- x ∈ a1 と仮定
        intro h_a1

        -- i a1 ha1 に ⟨x, hx⟩ が含まれることを導く。使ってない。
        have ground_lem:F.ground ∈ Finset.filter F.sets F.ground.powerset := by
          simp_all only [Finset.mem_filter, Finset.mem_powerset]
          constructor
          trivial
          exact F.has_ground

        have x_in_ground: x ∈ F.ground := by
          simp_all only [i] --
          simp_all only [Finset.mem_filter, Finset.mem_powerset]--
          --obtain ⟨left, right⟩ := pall
          obtain ⟨left_1, _⟩ := ha1
          --obtain ⟨left_2, right_2⟩ := ha2
          --simp_all only [ge_iff_le, n]
          apply left_1
          simp_all only

        have y_in_i_a1 : ⟨x, x_in_ground⟩  ∈ i a1 ha1 := by
          dsimp [i]
          simp only [Finset.mem_filter]
          constructor
          simp_all only [ true_and,Finset.mem_attach]
          use x
          use x_in_ground

        -- i a1 ha1 = i a2 ha2 より、i a2 ha2 にも含まれる
        --have _ : ⟨x, x_in_ground⟩ ∈ i a2 ha2 :=
        --  h_eq ▸ y_in_i_a1

  -- i a2 ha2 に含まれることから x ∈ a2 を導く
        simp_all only [Finset.mem_filter, exists_and_right, true_and,Finset.mem_attach, Subtype.mk.injEq,i]--
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        obtain ⟨w, h_1⟩ := y_in_i_a1
        obtain ⟨left_3, right_3⟩ := h_1
        obtain ⟨_, right_4⟩ := left_3
        subst right_4
        simp_all --only [n]

  -- a2 ⊆ a1 を示す部分
      · -- x ∈ a2 と仮定
        intro h_a2

        -- i a2 ha2 に ⟨x, hx⟩ が含まれることを導く
        have x_in_ground: x ∈ F.ground := by
          simp_all only [ i]
          simp_all only [Finset.mem_filter, Finset.mem_powerset]
          obtain ⟨left, right⟩ := pall
          obtain ⟨left_1, right_1⟩ := ha1
          obtain ⟨left_2, right_2⟩ := ha2
          simp_all only [n]
          apply left_2
          simp_all only
        have y_in_i_a2 : ⟨x, x_in_ground⟩ ∈ i a2 ha2 := by
          dsimp [i]
          simp only [Finset.mem_filter]
          constructor
          simp_all only [Finset.mem_attach]
          use x
          use x_in_ground
        have y_in_i_a1 : ⟨x, x_in_ground⟩ ∈ i a1 ha1 := by
          simp_all only [ Finset.mem_attach, i]

        -- i a1 ha1 に含まれることから x ∈ a1 を導く

        dsimp [i] at y_in_i_a1
        rw [Finset.mem_filter] at y_in_i_a1
        simp at y_in_i_a1
        exact y_in_i_a1.2

    -- 全射性の証明
    have suj : ∀ (b : Finset { x // x ∈ F.ground }) (_ : b ∈ Finset.image
      (λ s => Finset.filter (λ y => ∃ x, ∃ (hx : x ∈ F.ground), ⟨x, hx⟩ = y ∧ x ∈ s) F.ground.attach)
        (Finset.filter F.sets F.ground.powerset)),
      ∃ a, ∃ (ha: a ∈ Finset.filter F.sets F.ground.powerset), i a ha = b :=
      by
        intros b hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        exact ⟨a, ha, rfl⟩

    -- card_bij の適用
    exact Finset.card_bij i hi inj suj

open Finset

--variable {α : Type*} (FG : Finset α) (Fsets : Finset α → Prop)

--omit [Nonempty α] in
lemma FG_same_card (FG : Finset α) (Fsets : Finset α → Prop) [DecidablePred Fsets] (a : Finset α) (_ : a ∈ Finset.filter Fsets FG.powerset) (a_in_FG : a ⊆ FG) :
  FG.sum (fun x => if x ∈ a then 1 else 0) = ∑ a_1 in FG.attach, if ∃ x, (∃ (hx : x ∈ FG), ⟨x, hx⟩ = a_1) ∧ x ∈ a then 1 else 0 :=
by
  let f := λ x => if x ∈ a then 1 else 0
  let g := λ (a_1 : {x // x ∈ FG}) => if ∃ x, (∃ (_ : x ∈ FG), x = a_1) ∧ x ∈ a then 1 else 0

  let i := λ (x : α) (hx: x ∈ FG) => (⟨x, hx⟩ : {x // x ∈ FG})
  have hi: ∀ (a_1 :α) (hs: a_1 ∈ FG) , i a_1 hs ∈ FG.attach := by
    intro a_1 hs
    simp_all only [mem_filter, mem_powerset, true_and, mem_attach, i]

  have inj : ∀ (a_1 : α) (hs1 : a_1 ∈ FG) (a_2 : α)(hs2 : a_2 ∈ FG), i a_1 hs1 = i a_2 hs2 → a_1 = a_2 := by
    intro a_1 a_2 hs1 hs2 a_3
    simp_all only [ mem_attach, implies_true, Subtype.mk.injEq, i]

  have surj : ∀ (b : {x // x ∈ FG}), b ∈ FG.attach → ∃ a, ∃ (ha : a ∈ FG), i a ha = b := by
    intro b
    intro _
    simp_all only [mem_powerset, true_and, mem_attach, implies_true, Subtype.mk.injEq, i]
    obtain ⟨val, property⟩ := b
    simp_all only [Subtype.mk.injEq, exists_prop, exists_eq_right]


  have h : ∀ (x : α) (hx : x ∈ FG), f x = g ⟨x, hx⟩ := by
    intro x hx
    simp only [f, g, i, Subtype.exists, exists_prop, true_and]
    simp_all only [mem_filter, mem_powerset, exists_eq_right, i]
    split
    next h =>
      split
      next h_1 => simp_all only
      next h_1 => simp_all only [not_exists, not_and, not_true_eq_false, imp_false, forall_mem_not_eq']
    next h =>
      split
      next h_1 =>
        obtain ⟨w, h_1⟩ := h_1
        obtain ⟨left, right⟩ := h_1
        obtain ⟨_, right_1⟩ := left
        subst right_1
        simp_all only
      next h_1 => simp_all only [ not_false_eq_true,implies_true]
  --#check Finset.sum_bij
  let result := @Finset.sum_bij _ _ _ _ FG FG.attach f g i hi inj surj h
  dsimp [f,g,i] at result
  simp_all
  --result  (∑ x ∈ FG, if x ∈ a then 1 else 0) = ∑ x ∈ FG.attach, if ∃ x_1, (∃ (_ : x_1 ∈ FG), x_1 = ↑x) ∧ x_1 ∈ a then 1 else 0
  --goal  FG.sum (if x ∈ a then 1 else 0) = (filter (fun x => ∃ x_1, (∃ (hx : x_1 ∈ FG), ⟨x_1, hx⟩ = x) ∧ x_1 ∈ a) FG.attach).card
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_const]
  rw [Finset.sum_ite] at result
  rw [Finset.sum_const, nsmul_one] at result

  simp_all only [  Nat.cast_id, sum_const_zero, add_zero, sum_boole]--
  have sum_card :FG.sum (λ x => if x ∈ a then 1 else 0) = a.card := by
    have : FG.sum (λ x => if x ∈ a then 1 else 0) = (FG.filter (λ x => x ∈ a)).sum (λ _ => 1) := by
      rw [←Finset.sum_filter]
    rw [this]
    simp_all only [sum_ite_mem, sum_const, smul_eq_mul, mul_one]
    apply Finset.card_bij
    on_goal 2 => intro a₁ ha₁ a₂ ha₂ a_1
    on_goal 2 => ext1
    on_goal 2 => exact a_1
    intro a_1 ha_1
    simp_all only [mem_filter, mem_attach, true_and]
    obtain ⟨val, property⟩ := a_1
    obtain ⟨w, h_1⟩ := ha_1
    obtain ⟨left, right⟩ := h_1
    obtain ⟨_, right_1⟩ := left
    subst right_1
    simp_all only
    intro b a_1
    simp_all
    apply And.intro
    apply Exists.intro
    apply And.intro
    on_goal 2 => exact a_1
    simp_all only [and_true]
    exact a_in_FG a_1
    exact a_in_FG a_1
  simp_all
  have rewrite_lem:FG.sum (fun x => if x ∈ a then 1 else 0) = FG.sum (fun x => if x ∈ a then 1 else 0) := by
    simp
  have result_lem:(filter (fun x => x ∈ a) FG) = a := by
    simp_all only [sum_ite_mem, sum_const, smul_eq_mul, mul_one]
    ext1 a_1
    simp_all only [mem_filter, and_iff_right_iff_imp]
    intro a_2
    exact a_in_FG a_2
  rw [result_lem] at result
  simp_all only [sum_ite_mem, sum_const, smul_eq_mul, mul_one]
  congr
  ext x : 2
  obtain ⟨val, property⟩ := x
  simp_all only [Subtype.mk.injEq, exists_prop]
  simp_all only [Subtype.mk.injEq, implies_true, exists_prop, i, f, g]
  apply Iff.intro
  · intro a_1
    obtain ⟨w, h_1⟩ := a_1
    obtain ⟨left, right⟩ := h_1
    obtain ⟨left, right_1⟩ := left
    subst right_1
    simp_all only
  · intro a_1
    use val

--omit [Nonempty α] in
theorem card_sum_bijection (FG: Finset α) (Fsets: Finset α → Prop) [DecidablePred Fsets] :
  (Finset.filter Fsets FG.powerset).sum Finset.card =
    ∑ x in Finset.image (λ s => Finset.filter (λ y => ∃ x, ∃ (hx : x ∈ FG), ⟨x, hx⟩ = y ∧ x ∈ s) FG.attach)
    (Finset.filter (λ S => Fsets S) FG.powerset), x.card :=
by
  -- `s` と `t` の定義
  let s := Finset.filter Fsets FG.powerset
  let t := Finset.image (λ s => Finset.filter (λ y => ∃ x, ∃ (hx : x ∈ FG), ⟨x, hx⟩ = y ∧ x ∈ s) FG.attach)
            (Finset.filter (λ S => Fsets S) FG.powerset)

  -- 写像 `i` の定義とその性質
  let i := fun (s : Finset α) (_ : s ∈ Finset.filter Fsets FG.powerset) => Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ FG), ⟨x, x_1⟩ = y) ∧ x ∈ s) FG.attach
  -- `hi` の証明: `i` が `s` の各要素を `t` の要素に対応させることを示す
  have hi : ∀ (a : Finset α) (ha : a ∈ s), i a ha ∈ t :=
    by
      intro a ha
      simp_all only [exists_and_right, Finset.mem_image, i, t]--
      simp_all only [Finset.mem_filter, Finset.mem_powerset, s]
      obtain ⟨left, right⟩ := ha
      use a


  -- `i_inj` の証明: 単射性の証明
  have i_inj : ∀ (a₁: Finset α) (ha₁ : a₁ ∈ s),∀ (a₂ : Finset α) (ha₂ : a₂ ∈ s), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ :=
    by
      intro a1 ha1 a2 ha2 h_eq
      dsimp [i] at h_eq
      ext x
      apply Iff.intro
      · intro h
        have x_in_ground: x ∈ FG := by
          simp_all only [mem_filter, mem_powerset, exists_and_right, mem_image, and_imp, s, i, t]
          obtain ⟨left, _⟩ := ha1
          --obtain ⟨left_1, right_1⟩ := ha2
          apply left
          simp_all only

        have y_in_i_a1 : ⟨x, x_in_ground⟩  ∈ i a1 ha1 := by
          dsimp [i]
          simp only [Finset.mem_filter]
          constructor
          simp_all only [ Finset.mem_powerset,Finset.mem_attach]
          simp_all only [ Subtype.mk.injEq,exists_prop]--
          --obtain ⟨left, right⟩ := ha1
          --obtain ⟨left_1, right_1⟩ := ha2
          apply Exists.intro
          · apply And.intro
            on_goal 2 => {exact h
            }
            · simp_all only [and_self]

        simp_all only [mem_filter, mem_attach, Subtype.mk.injEq,true_and, i,s]--
        --上のsimp_allでy_in_i_a1が書き換えられている。どのルールで書き換えているのか、調査失敗。
        obtain ⟨w, h_1⟩ := y_in_i_a1
        obtain ⟨left_2, right_2⟩ := h_1
        obtain ⟨_, right_3⟩ := left_2
        subst right_3
        exact right_2
      · intro h
        have x_in_ground: x ∈ FG := by
          simp_all only [mem_filter, mem_powerset, exists_and_right, mem_image, and_imp, s, i, t]
          obtain ⟨left, _⟩ := ha2
          --obtain ⟨left_1, right_1⟩ := ha1
          apply left
          simp_all only

        have y_in_i_a2 : ⟨x, x_in_ground⟩  ∈ i a2 ha2 := by
          dsimp [i]
          simp only [Finset.mem_filter]
          constructor
          simp_all only [Finset.mem_filter,Finset.mem_attach]
          simp_all only [ Subtype.mk.injEq, exists_prop]
          apply Exists.intro
          · apply And.intro
            on_goal 2 => {exact h
            }
            · simp_all only [and_self]

        have y_in_i_a1 : ⟨x, x_in_ground⟩ ∈ i a1 ha1 := by
          simp_all only [i]

        dsimp [i] at y_in_i_a1
        rw [Finset.mem_filter] at y_in_i_a1
        obtain ⟨w, h_1⟩ := y_in_i_a1

        simp_all only [mem_filter,  Subtype.mk.injEq, true_and, i]--
        simp_all only [ mem_powerset, s]
        obtain ⟨w, h_2⟩ := y_in_i_a2
        obtain ⟨w_1, h_1⟩ := h_1
        obtain ⟨left_2, right_2⟩ := h_2
        obtain ⟨left_3, right_3⟩ := h_1
        obtain ⟨left_2, right_4⟩ := left_2
        obtain ⟨_, right_5⟩ := left_3
        subst right_4 right_5
        simp_all only


  -- `i_surj` の証明: 全射性の証明
  have i_surj : ∀ b ∈ t, ∃ a, ∃ (ha : a ∈ s), i a ha = b :=
    by
      intro b a
      simp_all only [exists_and_right, Finset.mem_image,  exists_prop, i, t]--

  -- 対応する要素のカード数が一致することの証明
  have h : ∀ (a : Finset α) (ha : a ∈ s), Finset.card a = Finset.card (i a ha) :=
    by
      intro a ha
      dsimp [i]
      simp only [Finset.card_filter]
      dsimp [s] at ha
      have a_in_FG: a ⊆ FG := by
        intro x
        intro hx
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        obtain ⟨left, _⟩ := ha
        exact left hx
      rw [←FG_same_card FG Fsets a ha a_in_FG]
      simp_all
      --simp_all only [implies_true, s, i, t]
      congr
      ext1 a_1
      simp_all only [subset_refl, mem_inter, iff_and_self]
      intro a_2
      exact a_in_FG a_2

  -- すべての仮定が整ったので、`Finset.sum_bij`を適用
  exact Finset.sum_bij i hi i_inj i_surj h

lemma fin_total_eq (F: IdealFamily α)(_ : F.ground.card ≥ 2) (hn: Fintype.card F.ground = F.ground.card):
  total_size_of_hyperedges (toIdealFinFamily F F.ground.card hn).toSetFamily = total_size_of_hyperedges F.toSetFamily := by

  let n := F.ground.card
  --fin_number_eqでも計算している。
  let embedding := (Fintype.equivFinOfCardEq hn).toFun
  --#check embedding { x // x ∈ F.ground } → Fin F.ground.card
  have hf: Function.Injective embedding := by
    simp_all only [embedding]
    exact (Fintype.equivFinOfCardEq hn).injective
  let GSet := (toIdealFinFamily F n hn).ground.powerset.filter (toIdealFinFamily F n hn).toSetFamily.sets
  let FSet: Finset (Finset α)  := F.ground.powerset.filter (λ S => F.toSetFamily.sets S)
  let projectToGround (x: α) (hx: x ∈ F.ground) : { x:α  // x ∈ F.ground } := ⟨x, hx⟩
  --haveI : DecidablePred (λ x => x ∈ F.ground) := inferInstance
  let projectFSetToGround (S : Finset (Finset α)) : Finset (Finset { x : α // x ∈ F.ground }) :=
    S.image (λ s => Finset.filter (λ y => ∃ (x : α) (hx : x ∈ F.ground), projectToGround x hx = y ∧ x ∈ s) (Finset.univ))
  let FSet2:Finset (Finset { x // x ∈ F.ground }) := projectFSetToGround FSet

  have hFG: GSet = FSet2.image (λ S => Finset.image embedding S) := by
    simp_all only [ge_iff_le, Equiv.toFun_as_coe]
    dsimp [FSet2, GSet,embedding]
    dsimp [projectFSetToGround]
    dsimp [projectToGround]
    dsimp [toIdealFinFamily,SetFamily.toFinFamily]
    simp
    dsimp [FSet]
    simp_all only [Equiv.toFun_as_coe, embedding, n]
    apply Finset.ext
    intro xx
    simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image] --
    constructor
    · intro h
      obtain ⟨left, right⟩ := h
      obtain ⟨w, h⟩ := right
      obtain ⟨left_1, right⟩ := h
      subst right
      use w --2回useを使う必要あり。
      simp_all only [and_true]
      use w.map (Function.Embedding.subtype _)
      simp_all only [Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right,exists_eq_right]--
      apply And.intro
      · apply And.intro
        · intro x hx
          simp_all only [Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right,exists_eq_right]--
          obtain ⟨w_1, _⟩ := hx
          simp_all only
        · convert left_1
          ext x a : 2
          simp_all only [Finset.mem_map, Function.Embedding.coe_subtype, Finset.mem_image]--
      · ext1 a
        simp_all only [Finset.mem_filter, Finset.mem_attach, true_and]
        obtain ⟨val, property⟩ := a
        simp_all only [Subtype.mk.injEq, exists_prop]
        apply Iff.intro
        · intro a
          obtain ⟨w_1, h⟩ := a
          --obtain ⟨left_2, right⟩ := h
          --obtain ⟨_, right_1⟩ := left_2
          --obtain ⟨w_2, h⟩ := right
          --subst right_1
          simp_all only
        · intro a
          apply Exists.intro
          · exact a
          · simp_all only [Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right,exists_eq_right]--
    · intro h
      obtain ⟨w, h⟩ := h
      obtain ⟨left, right⟩ := h
      subst right
      obtain ⟨left, right⟩ := left
      obtain ⟨w_1, h⟩ := right
      subst h
      constructor
      ·
        --obtain ⟨left_1, right⟩ := w_1
        intro x hx
        simp_all only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
          Subtype.mk.injEq,  exists_and_left, Finset.mem_map, Function.Embedding.coeFn_mk]--
        obtain ⟨w, h⟩ := hx
        obtain ⟨left_2, right_1⟩ := h
        --obtain ⟨w_1, h⟩ := left_2
        obtain ⟨w_2, h_1⟩ := right_1
        --obtain ⟨left_2, _⟩ := h
        --obtain ⟨_, right_2⟩ := left_2
        --subst h_1 right_2
        --simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop, exists_eq_right]
        subst h_1
        simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop, exists_eq_right]
      · --goal ∃ t,  F.sets (Finset.image Subtype.val t) ∧ ...
        use F.ground.attach.filter (λ x => x.1 ∈ left)
        obtain ⟨left_1, right⟩ := w_1
        apply And.intro
        · convert right
          ext1 a
          simp_all only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
            exists_and_left, exists_prop, exists_eq_right_right, and_iff_left_iff_imp]--
          intro a_1
          exact left_1 a_1
        · ext1 a
          simp_all only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,Subtype.mk.injEq,  exists_and_left]
          /-
          apply Iff.intro
          · intro a_1
            obtain ⟨w, h⟩ := a_1
            obtain ⟨left_2, right_1⟩ := h
            obtain ⟨w_1, h⟩ := left_2
            obtain ⟨w_2, h_1⟩ := right_1
            obtain ⟨left_2, right_1⟩ := h
            obtain ⟨_, right_2⟩ := left_2
            subst h_1 right_2
            simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop, exists_eq_right_right,and_self]
          · intro a_1
            obtain ⟨w, h⟩ := a_1
            obtain ⟨left_2, right_1⟩ := h
            obtain ⟨w_1, h⟩ := right_1
            subst h
            simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop, exists_eq_right_right,
              and_true]
            use w
          -/

  --#check same_summation FSet2 GSet embedding hf hFG
  have FG_sum_eq: FSet2.sum Finset.card = GSet.sum Finset.card:= by
    apply same_summation FSet2 GSet embedding hf hFG
  clear hFG
  dsimp [FSet2, GSet] at FG_sum_eq
  dsimp [projectFSetToGround] at FG_sum_eq
  dsimp [projectToGround] at FG_sum_eq
  dsimp [number_of_hyperedges, total_size_of_hyperedges]
  simp at FG_sum_eq
  --simp
  rw [←FG_sum_eq]
  dsimp [FSet]
  apply Eq.symm
  clear FG_sum_eq hf FSet2 GSet projectFSetToGround projectToGround embedding FSet

  let result := (card_sum_bijection F.ground F.toSetFamily.sets).symm
  rw [←result]
  clear result
  congr
  simp

theorem ideal_implies_average_rare (F : IdealFamily α) : normalized_degree_sum F.toSetFamily <= 0 := by
  set n := F.ground.card with n_def
  have hn: Fintype.card F.ground = n:= by
    simp_all only [Fintype.card_coe, n]
  by_cases h : n ≥ 2
  case pos =>
    let pall := P_all n h
    dsimp [P] at pall
    --#check F.toSetFamily.toFinFamily
    have hn2: (toIdealFinFamily F n hn).ground.card = n := by
      simp_all only [toIdealFinFamily, hn]
      let equal :=  equal_card_fin_ideal_family F hn
      --#check equal
      have equal2: Fintype.card { x // x ∈ (toIdealFinFamily F n hn).ground } = (toIdealFinFamily F n hn).ground.card := by
        exact Fintype.card_coe (toIdealFinFamily F n hn).ground
      simp_all only [n, equal]
      obtain ⟨_, right⟩ := pall
      simp_all only [ge_iff_le, n]
      rfl

    --let pa :=  pall.2 (toIdealFinFamily F n hn)
    let embedding := (Fintype.equivFinOfCardEq hn).toFun
    have hf: Function.Injective embedding := by
      simp_all only [embedding]
      exact (Fintype.equivFinOfCardEq hn).injective
    rw [normalized_degree_sum]
    simp
    let num := fin_number_eq F h hn
    let tot := fin_total_eq F h hn

    rw [←num,←tot]

    have ideal_n: (toIdealFinFamily F F.ground.card hn).ground.card = n:= by
      simp_all only [Equiv.toFun_as_coe, n, embedding]
    have normalized_fin: normalized_degree_sum (toIdealFinFamily F F.ground.card hn).toSetFamily ≤ 0 := by
      dsimp [normalized_degree_sum]
      simp_all only [Equiv.toFun_as_coe, tsub_le_iff_right, zero_add, n, embedding, tot, num]
      obtain ⟨_, right⟩ := pall

      let result := right (toIdealFinFamily F F.ground.card hn) ideal_n
      simp_all only [ge_iff_le]
      rw [normalized_degree_sum] at result
      simp at result
      simp_all only [n, tot, num]

    rw [normalized_degree_sum] at normalized_fin
    rw [tot,num] at normalized_fin
    simp_all only [Equiv.toFun_as_coe, tsub_le_iff_right, zero_add, n, embedding, tot, num]

    ---lemma fin_number_eq (F: IdealFamily α)(h : F.ground.card ≥ 2) (hn: Fintype.card F.ground = F.ground.card): number_of_hyperedges (toIdealFinFamily F F.ground.card hn).toSetFamily = number_of_hyperedges F.toSetFamily := by
    --let embedding2: Finset F.ground → Finset (Fin n) := λ S => S.image (Fintype.equivFinOfCardEq hn).toFun
    --ここにnumberの読み込み部分を作る。
    --それからtotalの計算部分を作って、ここから読み込む。
    --そして、normalized_degree_sumの計算部分を作る。

  case neg =>
    -- n < 2 の場合は、normalized_degree_sum F.toSetFamily <= 0 が自明

    have n_ge_1: n ≥ 1 := by
      rw [n_def]
      by_contra h
      have h3: F.ground.Nonempty := by
        exact F.nonempty_ground
      rw [←Finset.one_le_card] at h3
      linarith

    rw [normalized_degree_sum]
      --F.groundがnonemptyなので、nは1以上。

    have n4: n <= 1 := by
      simp_all only [ge_iff_le]
      linarith

    have n_eq_one: n = 1:= by
      symm
      rw [le_antisymm_iff]
      constructor
      exact n_ge_1
      exact n4

    --台集合の大きさが１のときは集合族が決定するので、normalized_degree_sumは0
    have n_eq_one2: Fintype.card F.ground = 1 := by
      rw [hn]
      exact n_eq_one

    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp n_eq_one2

    have ground_one : F.ground.attach = {a} := ha

    --下で使っている。
    have ground_one2: F.ground = {a.val} := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_singleton, Finset.mem_attach]
      constructor
    -- `x ∈ F.ground` の場合に `x = a.val` を示す
      intro hx
      simp_all only [n]
      obtain ⟨val, property⟩ := a
      --simp_all only
      --goal x = val
      --have val_in_ground: val ∈ F.ground := by
      -- propertyで、x in F.groundが示されている。a in F.ground
      -- hx: x in F.ground  property: val ∈ F.ground F.ground.card = 1より、val = x
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hn.symm
      have hx' : x = y := by simp_all only [Finset.card_singleton, Finset.mem_singleton]
      have hval' : val = y := by
        subst hx'
        simp_all only [Finset.mem_singleton]
        rw [hy] at property
        simp_all only [Finset.mem_singleton]

      exact Eq.trans hx' hval'.symm

      intro a_1
      subst a_1
      simp only [Finset.univ_eq_attach, Finset.coe_mem]

    have all_sets: F.ground.powerset = {{a.val},∅} := by
      simp_all only [Finset.mem_singleton]
      obtain ⟨val, property⟩ := a
      simp_all only
      ext1 a
      simp only [Finset.mem_powerset, Finset.subset_singleton_iff, Finset.mem_insert, Finset.mem_singleton] --
      apply Iff.intro
      · intro a_1
        cases a_1 with
        | inl h =>
          subst h
          simp_all only [or_true]
        | inr h_1 =>
          subst h_1
          simp only [Finset.singleton_ne_empty, or_false]--
      · intro a_1
        cases a_1 with
        | inl h =>
          subst h
          simp only [Finset.singleton_ne_empty, or_true]
        | inr h_1 =>
          subst h_1
          simp only [true_or]

    --下で使っているよう。
    have hyperedges_one: ∀ S:Finset α, F.sets S ↔ S = {a.val} ∨ S = ∅ := by
      intro S
      apply Iff.intro
      intro hS
      simp_all only [ground_one, Finset.mem_singleton, Finset.mem_attach]
      --unfold SetFamily.sets at hS --setsの定義の中で展開するときにunfoldを使う。
      have hG: F.sets F.ground := by
        exact F.has_ground
      have inc: S ⊆ F.ground := F.toSetFamily.inc_ground S hS
      have S_eq: S = {a.val} ∨ S = ∅ := by
        simp_all only [Finset.mem_singleton, Finset.mem_attach]
        by_cases h: S = ∅
        subst h
        simp_all only [  or_true]
        simp_all only [ Finset.subset_singleton_iff, false_or,or_false]--
      simp_all only [Finset.univ_eq_attach, Finset.subset_singleton_iff]
      ----
      intro hS
      cases hS with
      | inr hs =>
        rw [hs]
        exact F.has_empty
      | inl hs =>
        rw [hs]
        rw [←ground_one2]
        exact F.has_ground

    have num: number_of_hyperedges F.toSetFamily = 2 := by
      rw [number_of_hyperedges]
      simp_all only [Finset.univ_eq_attach]
      obtain ⟨val, property⟩ := a
      simp_all only
      symm
      simp [Finset.filter_true_of_mem, hyperedges_one]

    have tot: total_size_of_hyperedges F.toSetFamily = 1 := by
      dsimp [Ideal.total_size_of_hyperedges]
      --simp_all only [ Finset.univ_eq_attach]
      obtain ⟨val, property⟩ := a
      simp_all only
      simp [Finset.filter_true_of_mem, hyperedges_one]

    simp_all only [le_refl, Nat.cast_one, one_mul, Nat.cast_ofNat,mul_one, sub_self, n] --

  end Ideal
