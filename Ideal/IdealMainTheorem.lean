--Ideal集合族が平均abundantにならないことの証明。IdealMainのほうは、各Fin n上のIdeal集合族に対して、平均abundantにならないことを示した。
--ここでは、一般のalpha上のIdeal集合族に対して、平均abundantにならないことを示したい。
--alpha上のIdeal集合族をFin n上のIdeal集合族に埋め込む関数を定義したが、大きい方から小さい方への埋め込みは、思いのほか大変だった。
--数学的には、hyperedgeの数も、hyperedgeの大きさの和も埋め込みで変化がないことは自明だが、Leanで証明すると大変だった。
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

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

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
      obtain ⟨_, right⟩ := pall
      simp_all only [ge_iff_le, n]
      rfl

    --let pa :=  pall.2 (toIdealFinFamily F n hn)
    let embedding := (Fintype.equivFinOfCardEq hn).toFun
    have hf: Function.Injective embedding := by
      simp_all only [embedding]
      exact (Fintype.equivFinOfCardEq hn).injective--simp [number_of_hyperedges, toIdealFinFamily, equal_card_fin_ideal_family]
      --theorem same_cardinality [DecidableEq α] [DecidableEq β] (hf : Function.Injective f)(hFG : ∀ (T : Finset β), T ∈ GSet ↔ ∃ (S : Finset α),S ∈ FSet ∧ T = S.image f) :
      -- FSet.card = GSet.card
      --α = Fin n, β = Finset { x// x ∈ F.ground}, f = embedding, FSet = F.ground.powerset.filter F.toSetFamily.sets, GSet = (toIdealFinFamily F n hn).ground.powerset.filter (toIdealFinFamily F n hn).toSetFamily.sets
      --#check same_cardinality
    let GSet := (toIdealFinFamily F n hn).ground.powerset.filter (toIdealFinFamily F n hn).toSetFamily.sets
    let FSet: Finset (Finset α)  := F.ground.powerset.filter (λ S => F.toSetFamily.sets S)
    let projectToGround (x: α) (hx: x ∈ F.ground) : { x:α  // x ∈ F.ground } := ⟨x, hx⟩
    --projectToGround x (Finset.mem_of_subset hS hx))  -- else F.ground.choose :  {x : α // x ∈ F.ground }
    haveI : DecidablePred (λ x => x ∈ F.ground) := inferInstance
    --let projectToGroundImage (S : Finset α)(hS: S ⊆ F.ground) : Finset { x : α // x ∈ F.ground }  :=F.ground.attach.filter (fun x => x.1 ∈ S)
    let projectFSetToGround (S : Finset (Finset α)) : Finset (Finset { x : α // x ∈ F.ground }) :=
      S.image (λ s => Finset.filter (λ y => ∃ (x : α) (hx : x ∈ F.ground), projectToGround x hx = y ∧ x ∈ s) (Finset.univ))
    let FSet2:Finset (Finset { x // x ∈ F.ground }) := projectFSetToGround FSet


    --#check @same_cardinality ({x // x ∈ F.ground}) (Fin n)  _ _ FSet2 GSet
    have hFG : ∀ (T : Finset (Fin n)), (toIdealFinFamily F n hn).sets T ↔ ∃ (S : Finset { x // x ∈ F.ground }), F.toSetFamily.sets (S.map (Function.Embedding.subtype _)) ∧ T = S.image embedding := by

      intro T
      simp_all only [toIdealFinFamily, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton]
      simp_all only [Equiv.toFun_as_coe, n, embedding]
      obtain ⟨left, right⟩ := pall
      simp_all only [ge_iff_le, n]
      apply Iff.intro
      · intro a
        let ⟨S, hS⟩ := a
        obtain ⟨h1, h2⟩ := hS
        cases h2
        simp_all only [Equiv.toFun_as_coe]
        --goal ∃ S_1,  F.sets (Finset.map (Function.Embedding.subtype fun x => x ∈ F.ground) S_1) ∧ Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) S_1
        use S
        simp_all only [Equiv.toFun_as_coe]
        simp_all only [and_true]
        convert h1
        ext x a : 2
        simp_all only [Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right,
          exists_eq_right, Finset.mem_image]

      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left_1, right_1⟩ := h
        subst right_1
        have left_2 := left_1
        simp_all only
        have left_2 := left_2
        simp_all only
        have left_2 := left_2
        simp_all only
        have left_2 := left_2
        simp_all only
        convert left_2
        simp_all only [iff_true]
        have left_2 := left_2
        simp_all only
        have left_2 := left_2
        simp_all only
        have left_2 := left_2
        simp_all only
        have left_2 := left_2
        simp_all only
        use w
        simp_all only [Equiv.toFun_as_coe, and_true]
        have left_2 := left_2
        simp_all only
        rw [Finset.image]
        simp only [Multiset.toFinset_map]
        simp_all only [Finset.val_toFinset]
        rw [Finset.image]
        simp only [Multiset.toFinset_map]
        simp_all only [Finset.val_toFinset]
        convert left
        simp_all only [ge_iff_le, iff_true, n]
        simp only [Finset.image]
        simp_rw [Multiset.toFinset_map]
        simp_all only [Finset.val_toFinset]
        rw [Finset.image]
        rw [Multiset.toFinset_map]
        simp_all only [Finset.val_toFinset]
        convert left_2
        funext x
        ext z
        simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Finset.mem_map,
          Function.Embedding.coe_subtype]

    have hFG2: ∀ (T : Finset (Fin n)), T ∈ GSet ↔ ∃ S ∈ FSet2, T = Finset.image embedding S:= by
      dsimp [FSet2, projectFSetToGround]
      dsimp[projectToGround]
      dsimp [FSet,GSet]
      simp
      -- goal: ∀ (T : Finset (Fin n)),  T ⊆ (toIdealFinFamily F n hn).ground ∧ (toIdealFinFamily F n hn).sets T ↔ ∃ a, (a ⊆ F.ground ∧ F.sets a) ∧ T = Finset.image embedding (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ a) F.ground.attach)
      intro T
      simp_all only [toIdealFinFamily, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_singleton, Finset.mem_image, Finset.mem_map, Finset.mem_univ, Finset.mem_singleton]
      simp_all only [Equiv.toFun_as_coe, n, embedding]
      obtain ⟨left, right⟩ := pall
      simp_all only [ge_iff_le, n]
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
        simp_all only [and_true, Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right,
          exists_eq_right]
        apply And.intro
        · intro x hx
          simp_all only [Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists, exists_and_right,
            exists_eq_right]
          obtain ⟨w_1, _⟩ := hx
          simp_all only
        · ext1 a
          simp_all only [Finset.mem_image, Subtype.exists, Finset.mem_filter, Finset.mem_attach, true_and,
            Subtype.mk.injEq, exists_prop, exists_and_left]
          apply Iff.intro
          · intro a_1
            obtain ⟨w_1, h⟩ := a_1
            obtain ⟨w_2, h⟩ := h
            obtain ⟨left_4, right_2⟩ := h
            subst right_2
            simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop, exists_eq_right_right,
              and_true]
            apply Exists.intro
            · apply And.intro
              · apply And.intro
                on_goal 2 => {rfl
                }
                · simp_all only
              · simp_all only [exists_const]
          · intro a_1
            obtain ⟨w_1, h⟩ := a_1
            obtain ⟨left_4, right_2⟩ := h
            obtain ⟨w_2, h⟩ := left_4
            obtain ⟨w_3, h_1⟩ := right_2
            obtain ⟨left_4, right_2⟩ := h
            obtain ⟨_, right_3⟩ := left_4
            obtain ⟨w_4, h⟩ := right_2
            subst right_3 h_1
            simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_and_right, exists_eq_right,
              exists_const]
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
              simp_all only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
                Function.Embedding.coe_subtype, Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right,
                S]
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
                  Function.Embedding.coe_subtype, Subtype.exists, exists_and_left, exists_prop,
                  exists_eq_right_right, S]
              -- down_closed の性質を適用
              simp_all only [S]
              convert left_1
              ext1 a
              simp_all only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
                Function.Embedding.coe_subtype, Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right,
                and_iff_left_iff_imp]
              intro a_1
              exact ha a_1

          · --goal Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun y => ∃ x, (∃ (x_1 : x ∈ F.ground), ⟨x, x_1⟩ = y) ∧ x ∈ w) F.ground.attach) = Finset.image (⇑(Fintype.equivFinOfCardEq hn)) (Finset.filter (fun x => ↑x ∈ w) F.ground.attach)
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

        -- i a1 ha1 に ⟨x, hx⟩ が含まれることを導く
        have ground_lem:F.ground ∈ Finset.filter F.sets F.ground.powerset := by
          simp_all only [Finset.mem_filter, Finset.mem_powerset]
          constructor
          trivial
          exact F.has_ground

        have x_in_ground: x ∈ F.ground := by
          simp_all only [Equiv.toFun_as_coe, Finset.mem_filter, Finset.mem_powerset, exists_and_right,
            Finset.univ_eq_attach, Finset.mem_image, exists_exists_and_eq_and, and_imp, n, embedding, GSet, FSet2,
            projectFSetToGround, projectToGround, FSet, i]
          simp_all only [Finset.mem_filter, Finset.mem_powerset]
          obtain ⟨left, right⟩ := pall
          obtain ⟨left_1, right_1⟩ := ha1
          obtain ⟨left_2, right_2⟩ := ha2
          simp_all only [ge_iff_le, n]
          apply left_1
          simp_all only

        have y_in_i_a1 : ⟨x, x_in_ground⟩  ∈ i a1 ha1 := by
          dsimp [i]
          simp only [Finset.mem_filter]
          constructor
          simp_all only [Equiv.toFun_as_coe, Finset.mem_filter, Finset.mem_powerset, exists_and_right,
            Finset.univ_eq_attach, Finset.mem_image, exists_exists_and_eq_and, and_imp, subset_refl, true_and,
            Finset.mem_attach, n, embedding, GSet, FSet2, projectFSetToGround, projectToGround, FSet, i]
          use x
          use x_in_ground

        -- i a1 ha1 = i a2 ha2 より、i a2 ha2 にも含まれる
        --have _ : ⟨x, x_in_ground⟩ ∈ i a2 ha2 :=
        --  h_eq ▸ y_in_i_a1

  -- i a2 ha2 に含まれることから x ∈ a2 を導く
        simp_all only [Equiv.toFun_as_coe, Finset.mem_filter, Finset.mem_powerset, exists_and_right,
          Finset.univ_eq_attach, Finset.mem_image, exists_exists_and_eq_and, and_imp, subset_refl, true_and,
          Finset.mem_attach, Subtype.mk.injEq, exists_prop, and_self, n, embedding, GSet, FSet2,
          projectFSetToGround, projectToGround, FSet, i]
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        --obtain ⟨left, right⟩ := pall
        --obtain ⟨left_1, right_1⟩ := ha1
        --obtain ⟨left_2, right_2⟩ := ha2
        obtain ⟨w, h_1⟩ := y_in_i_a1
        obtain ⟨left_3, right_3⟩ := h_1
        obtain ⟨_, right_4⟩ := left_3
        subst right_4
        simp_all only [ge_iff_le, n]

  -- a2 ⊆ a1 を示す部分
      · -- x ∈ a2 と仮定
        intro h_a2

        -- i a2 ha2 に ⟨x, hx⟩ が含まれることを導く
        have x_in_ground: x ∈ F.ground := by
          simp_all only [Equiv.toFun_as_coe, Finset.mem_filter, Finset.mem_powerset, exists_and_right,
            Finset.univ_eq_attach, Finset.mem_image, exists_exists_and_eq_and, and_imp, n, embedding, GSet, FSet2,
            projectFSetToGround, projectToGround, FSet, i]
          simp_all only [Finset.mem_filter, Finset.mem_powerset]
          obtain ⟨left, right⟩ := pall
          obtain ⟨left_1, right_1⟩ := ha1
          obtain ⟨left_2, right_2⟩ := ha2
          simp_all only [ge_iff_le, n]
          apply left_2
          simp_all only
        have y_in_i_a2 : ⟨x, x_in_ground⟩ ∈ i a2 ha2 := by
          dsimp [i]
          simp only [Finset.mem_filter]
          constructor
          simp_all only [Equiv.toFun_as_coe, Finset.mem_filter, Finset.mem_powerset, exists_and_right,
            Finset.univ_eq_attach, Finset.mem_image, exists_exists_and_eq_and, and_imp, subset_refl, true_and,
            Finset.mem_attach, n, embedding, GSet, FSet2, projectFSetToGround, projectToGround, FSet, i]
          use x
          use x_in_ground
        have y_in_i_a1 : ⟨x, x_in_ground⟩ ∈ i a1 ha1 := by
          simp_all only [Equiv.toFun_as_coe, Finset.mem_filter, Finset.mem_powerset, exists_and_right,
            Finset.univ_eq_attach, Finset.mem_image, exists_exists_and_eq_and, and_imp, Finset.mem_attach,
            Subtype.mk.injEq, exists_prop, true_and, and_self, n, embedding, GSet, FSet2, projectFSetToGround,
            projectToGround, FSet, i]

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
        congr
        exact Fintype.card_coe (toIdealFinFamily F n hn).ground
      simp_all only [n, equal]
      obtain ⟨left, right⟩ := pall
      simp_all only [ge_iff_le, n]
      rfl

    let pa :=  pall.2 (toIdealFinFamily F n hn)
    let embedding := (Fintype.equivFinOfCardEq hn).toFun
    have hf: Function.Injective embedding := by
      simp_all only [embedding]
      exact (Fintype.equivFinOfCardEq hn).injective
    --let embedding2: Finset F.ground → Finset (Fin n) := λ S => S.image (Fintype.equivFinOfCardEq hn).toFun

  case neg =>
    -- n < 2 の場合は、normalized_degree_sum F.toSetFamily <= 0 が自明

    have n_ge_1: n ≥ 1 := by
      rw [n_def]
      by_contra h
      have h2: n = 0 := by
        simp_all only [Fintype.card_coe, ge_iff_le, not_le, Finset.one_le_card, Finset.not_nonempty_iff_eq_empty,
          Finset.card_empty, n]
      have h3: F.ground.Nonempty := by
        exact F.nonempty_ground
      simp_all only [Fintype.card_coe, ge_iff_le, not_le, Finset.one_le_card, not_true_eq_false, n]

    simp_all only [normalized_degree_sum]
      --F.groundがnonemptyなので、nは1以上。

    have n4: n <= 1 := by
      simp_all only [Fintype.card_coe, ge_iff_le, not_le, Finset.one_le_card, n]
      linarith

    have n_eq_one: n = 1:= by
      simp_all only [Fintype.card_coe, ge_iff_le, not_le, Finset.one_le_card, n]
      symm
      rw [le_antisymm_iff]
      simp_all only [Finset.one_le_card, and_self]

    --台集合の大きさが１のときは集合族が決定するので、normalized_degree_sumは0
    have n_eq_one2: Fintype.card F.ground = 1 := by
      simp_all only [Fintype.card_coe, ge_iff_le, not_le, Finset.one_le_card, n]

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
      simp_all only [ge_iff_le, not_le, le_refl, Fintype.card_coe, Finset.univ_eq_attach, n]
      obtain ⟨val, property⟩ := a
      simp_all only
      --goal x = val
      --have val_in_ground: val ∈ F.ground := by
      --  simp_all only
      -- propertyで、x in F.groundが示されている。a in F.ground
      -- hx: x in F.ground  property: val ∈ F.ground F.ground.card = 1より、val = x
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hn.symm
      have hx' : x = y := by simp_all only [Finset.card_singleton, Nat.one_lt_ofNat, Finset.mem_singleton]
      have hval' : val = y := by
        subst hx'
        simp_all only [Finset.card_singleton, Nat.one_lt_ofNat, Finset.mem_singleton]
        rw [hy] at property
        simp_all only [Finset.mem_singleton]

      exact Eq.trans hx' hval'.symm

    --下で使っているよう。
    have hyperedges_one: F.toSetFamily.sets = λ S => S = {a.val} ∨ S = ∅ := by
      ext S
      simp_all only [IdealFamily.toSetFamily, ground_one, Finset.mem_singleton, Finset.mem_attach]
      apply Iff.intro
      · intro h
        simp_all only [Fintype.card_ofSubsingleton, ge_iff_le, Nat.not_ofNat_le_one, not_false_eq_true, le_refl,
          Finset.card_singleton, Finset.univ_eq_attach, n]
        obtain ⟨val, property⟩ := a
        simp_all only

        --goal S = {val}
        --これは間違いでは。Sは
      · intro h
        --goal F.1.sets S
        subst h
        simp_all only [Fintype.card_ofSubsingleton, ge_iff_le, Nat.not_ofNat_le_one, not_false_eq_true, le_refl,
          Finset.card_singleton, Finset.univ_eq_attach, n]
        have ground_has: F.1.sets F.ground := by
          exact F.has_ground
        simp_all only


    have num: number_of_hyperedges F.toSetFamily = 2 := by
      rw [number_of_hyperedges]
      simp_all only [n_eq_one2, normalized_degree_sum, n_eq_one, Fintype.card_coe, ge_iff_le, not_le, Finset.one_le_card, n]
      simp_all only [Nat.one_lt_ofNat, Finset.singleton_nonempty, le_refl, Finset.card_singleton,
        Finset.univ_eq_attach]
      obtain ⟨val, property⟩ := a
      simp_all only
      simp [Finset.filter_true_of_mem]

    have tot: total_size_of_hyperedges F.toSetFamily = 1 := by
      dsimp [Ideal.total_size_of_hyperedges]
      simp_all only [n_eq_one2, normalized_degree_sum, n_eq_one, Fintype.card_coe, ge_iff_le, not_le, Finset.one_le_card, n]
      simp_all only [Nat.one_lt_ofNat, Finset.singleton_nonempty, le_refl, Finset.card_singleton,
        Finset.univ_eq_attach]
      obtain ⟨val, property⟩ := a
      simp_all only
      symm
      symm
      symm
      simp [← hyperedges_one]
      simp_all only
      simp [← hyperedges_one]
      simp_all only
      simp [← hyperedges_one]
      simp_all only
      simp [Finset.filter_true_of_mem]
      rfl
    --have h := P_all 2 (by decide)
    --exact h (toIdealFinFamily F 2 (by decide))

  end Ideal
