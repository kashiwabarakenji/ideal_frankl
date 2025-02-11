import LeanCopilot
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import rooted.CommonDefinition
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Finset.Union
import Mathlib.Tactic
import rooted.CommonDefinition
import rooted.RootedCircuits
import rooted.RootedImplication
import rooted.ClosureOperator
import rooted.RootedFrankl
import rooted.RootedSets
import rooted.Preorder

variable {α : Type}  [DecidableEq α] [Fintype α]

open Classical

noncomputable def root_vertices_sizeone (SF: ClosureSystem α)[DecidablePred SF.sets] (s: Finset SF.ground) : Finset SF.ground :=
  let RS := rootedSetsFromSetFamily SF.toSetFamily
(SF.ground.filter (fun x  => x ∈ (s.image Subtype.val) ∧ ∃ (r : ValidPair α), r ∈ RS.rootedsets ∧ r.root = x ∧ r.stem ⊆ s.image Subtype.val)).subtype (fun x => x ∈ SF.ground)

noncomputable def dash (SF: ClosureSystem α)[DecidablePred SF.sets]  (s: Finset SF.ground) : Finset SF.ground :=
closureOperator SF (root_vertices_sizeone SF s )

noncomputable def cover (SF: ClosureSystem α)[DecidablePred SF.sets]  (A B : Finset α) : Prop := SF.sets A ∧ SF.sets B ∧ A ⊂ B ∧ (∀ C :Finset α, SF.sets C → A ⊆ C → A ⊆ B → C = A ∨ C = B)

-- `B` をカバーする `A` すべての共通部分を求める関数 -/
noncomputable def coveringIntersection {α : Type} [DecidableEq α] [Fintype α] (SF: ClosureSystem α)[DecidablePred SF.sets] (B : Finset α): Finset α :=
  finsetIntersection ((SF.ground.powerset.filter (fun s => (SF.sets s ∧ (cover SF s B)) ∨ s = B)))

noncomputable def coveringIntersection_sub {α : Type} [DecidableEq α] [Fintype α]  [Fintype α] (SF: ClosureSystem α) [DecidablePred SF.sets] (B : Finset SF.ground): Finset SF.ground :=
  (@coveringIntersection α _ _ SF _ (B.image Subtype.val)).subtype (fun x => x ∈ SF.ground)

lemma monotone_root_vertices_sizeone (SF: ClosureSystem α)[DecidablePred SF.sets]  (A B : Finset SF.ground):A ⊆ B → root_vertices_sizeone SF A ⊆ root_vertices_sizeone SF B:=
by
  intro hab
  dsimp [root_vertices_sizeone]
  intro x hx
  rw [Finset.subtype]
  rw [Finset.subtype] at hx
  simp at hx
  simp
  obtain ⟨a, h1⟩ := hx
  obtain ⟨h11,h12⟩ := h1.1
  obtain ⟨h121,h122⟩ := h1
  use a
  constructor
  · use h122
  · constructor
    · constructor
      · exact h12
      · constructor

        · obtain ⟨h1211, h1212⟩ := h121.1
          obtain ⟨h12111,h12112⟩ := h1212.1
          use h12111
          subst h122
          simp_all only [exists_const, and_self, true_and]
          obtain ⟨w, h⟩ := h1212
          obtain ⟨left, right⟩ := h
          obtain ⟨left_1, right⟩ := right
          subst left_1
          exact hab h12112

        · obtain ⟨h111,h112⟩ := h11.2
          obtain ⟨r,hr⟩ := h112
          use r
          constructor
          ·  exact hr.1

          · constructor
            ·
              subst h122
              simp_all only [exists_true_left, and_true, true_and, exists_prop, and_self_left, exists_const]

            · let hr2 := hr.2.2
              have :Finset.image Subtype.val A ⊆ Finset.image Subtype.val B :=
              by
                simp_all only [exists_true_left, and_true, true_and, exists_prop, and_self_left, exists_const]
                intro x hx
                simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
                obtain ⟨w_1, h⟩ := hx
                simp_all only [exists_true_left]
                exact hab h

              exact fun ⦃a⦄ a_1 => this (hr2 a_1)

    · subst h122
      simp_all only [exists_true_left, and_true, true_and, exists_prop, and_self_left]

lemma monotone_dash (SF: ClosureSystem α)[DecidablePred SF.sets]  (A B : Finset SF.ground):A ⊆ B → dash SF A ⊆ dash SF B:=
by
  dsimp [dash]
  intro hab
  let cml := monotone_from_SF_finset SF (root_vertices_sizeone SF A) (root_vertices_sizeone SF B)
  have :root_vertices_sizeone SF A ⊆ root_vertices_sizeone SF B :=
  by
    exact monotone_root_vertices_sizeone SF A B hab
  specialize cml this
  simp_all only


--open Finset

/--
`injective_cover`:
  閉包系 SF において、`cover SF Y1 X1` と `cover SF Y2 X2` が成立し
  さらに `Y1 = Y2` かつ `(X1 \ Y1) ∩ (X2 \ Y2)` が空でないならば、
  `X1 = X2` となることを示す。
-/
lemma injective_cover (SF : ClosureSystem α) [DecidablePred SF.sets]
    (X1 X2 Y1 Y2 : Finset α)
    (c1 : cover SF Y1 X1) (c2 : cover SF Y2 X2)
    (hY : Y1 = Y2)
    (h_nonempty : ((X1 \ Y1) ∩ (X2 \ Y2)).Nonempty) : X1 = X2 := by

  /- まず `Y1 = Y2` を書き換え -/
  rw [←hY] at c2

  /- `c1`, `c2` から被覆の成分を取り出す -/
  obtain ⟨hY1, hX1, hY1_ss_X1, cover_cond1⟩ := c1
  obtain ⟨hY1', hX2, hY1_ss_X2, cover_cond2⟩ := c2

  /- SF の交叉閉性： X1 ∩ X2 も SF.sets に属する -/
  have h_inter : SF.sets (X1 ∩ X2) := SF.intersection_closed X1 X2 hX1 hX2

  /- Y1 ⊆ X1, Y1 ⊆ X2 より Y1 ⊆ X1 ∩ X2 -/
  have hY1_sub_inter : Y1 ⊆ X1 ∩ X2 := by
    rw [@Finset.subset_inter_iff]
    constructor
    rw [Finset.ssubset_def] at hY1_ss_X1
    exact hY1_ss_X1.1

    rw [Finset.ssubset_def] at hY1_ss_X2
    exact subset_of_ssubset hY1_ss_X2

  /- X1 ∩ X2 ⊆ X1, X1 ∩ X2 ⊆ X2 は自明 -/
  have h_inter_sub_X1 : X1 ∩ X2 ⊆ X1 := by
    subst hY
    simp_all only [Finset.inter_subset_left]
  have h_inter_sub_X2 : X1 ∩ X2 ⊆ X2 := by
    subst hY
    simp_all only [Finset.inter_subset_left, Finset.inter_subset_right]

  /- (X1 \ Y1) ∩ (X2 \ Y1) が非空 ⇒ X1 ∩ X2 は Y1 と一致しないことを示す -/
  obtain ⟨x, hx⟩ := h_nonempty
  have hx_in_X1X2 : x ∈ X1 ∩ X2 := by
    -- x ∈ X1 \ Y1 および x ∈ X2 \ Y1 から x ∈ X1 ∩ X2 を取り出す
    subst hY
    simp_all only [Finset.inter_subset_left, Finset.inter_subset_right, Finset.mem_inter, Finset.mem_sdiff, and_self]
  have hx_not_in_Y1 : x ∉ Y1 := by
    -- x ∈ X1 \ Y1 なので x ∉ Y1
    subst hY
    simp_all only [Finset.inter_subset_left, Finset.inter_subset_right, Finset.mem_inter, Finset.mem_sdiff, true_and,
      and_self, not_false_eq_true]

  -- したがって X1 ∩ X2 は Y1 を真に含む
  -- よって X1 ∩ X2 ≠ Y1
  have h_diff : X1 ∩ X2 ≠ Y1 := fun h_eq => by
    rw [← h_eq] at hx_not_in_Y1
    subst h_eq hY
    simp_all only [Finset.inter_subset_left, Finset.inter_subset_right]

  /-
    ここで「被覆の性質 (cover_cond1)」を X1 ∩ X2 に適用:
    cover_cond1 は
      (∀ C, SF.sets C → Y1 ⊆ C → C ⊆ X1 → C = Y1 ∨ C = X1)
    という形。
    今回 C := X1 ∩ X2 が
      (1) SF.sets(C) : h_inter
      (2) Y1 ⊆ C     : hY1_sub_inter
      (3) C ⊆ X1     : h_inter_sub_X1
    を満たすので適用できる。
  -/
  have cover_res1 : X1 ∩ X2 = Y1 ∨ X1 ∩ X2 = X1 :=
  by
    apply cover_cond1 (X1 ∩ X2) h_inter hY1_sub_inter --h_inter_sub_X1
    subst hY
    simp_all only [Finset.inter_subset_left, Finset.inter_subset_right, Finset.mem_inter, ne_eq, Finset.mem_sdiff,
      not_false_eq_true, and_self]
    obtain ⟨left, right⟩ := hx_in_X1X2
    intro y hy
    exact hY1_ss_X1.1 hy

  /- 場合分け -/
  cases cover_res1 with
  | inl eq_to_Y1 =>
    -- X1 ∩ X2 = Y1 とすると h_diff に反する
    contradiction
  | inr eq_to_X1 =>
    -- X1 ∩ X2 = X1 なので X1 ⊆ X2
    have h_X1_sub_X2 : X1 ⊆ X2 := by
      rw [← eq_to_X1]
      subst hY
      simp_all only [subset_refl, ne_eq, Finset.inter_eq_left, Finset.mem_inter, Finset.mem_sdiff, not_false_eq_true,
        and_self, and_true, true_and, Finset.inter_subset_right]

    /-
      同様に cover_cond2 を X1 ∩ X2 に適用:
      (∀ C, SF.sets C → Y1 ⊆ C → C ⊆ X2 → C = Y1 ∨ C = X2)
      C := X1 ∩ X2 が
        SF.sets(C) : h_inter
        Y1 ⊆ C     : hY1_sub_inter
        C ⊆ X2     : h_inter_sub_X2
      を満たすので適用可能
    -/
    have cover_res2 : X1 ∩ X2 = Y1 ∨ X1 ∩ X2 = X2 :=
    by
      apply cover_cond2 (X1 ∩ X2) h_inter hY1_sub_inter --h_inter_sub_X2
      subst hY
      simp_all only [subset_refl, ne_eq, Finset.inter_eq_left, Finset.mem_inter, Finset.mem_sdiff, not_false_eq_true,
        and_self, and_true, true_and, forall_const]
      exact hY1_sub_inter.trans h_X1_sub_X2


    cases cover_res2 with
    | inl eq_to_Y1' =>
      -- X1 ∩ X2 = Y1 は再度 h_diff に反する
      contradiction
    | inr eq_to_X2 =>
      -- X1 ∩ X2 = X2 なので X2 ⊆ X1
      have h_X2_sub_X1 : X2 ⊆ X1 := by
        rw [← eq_to_X2]
        subst hY
        simp_all only [subset_refl, ne_eq, Finset.inter_self, Finset.mem_sdiff, not_false_eq_true, and_self]

      -- X1 ⊆ X2 かつ X2 ⊆ X1 なので結局 X1 = X2
      exact le_antisymm h_X1_sub_X2 h_X2_sub_X1

lemma maximal_hyperedge_exists (SF:ClosureSystem α)  [DecidablePred SF.sets] (X:Finset α) (x :α) (SFX: SF.sets X) (hx: x ∈ X \ (coveringIntersection SF X)):
   ∃ (Y :Finset α), SF.sets Y ∧ x ∈ X \ Y ∧ cover SF Y X:=
by
  dsimp [coveringIntersection] at hx
  rw [@Finset.mem_sdiff] at hx
  rw [mem_finsetIntersection_iff_of_nonempty] at hx
  let hx2 := hx.2
  simp at hx2
  obtain ⟨Y, hY⟩ := hx2
  use Y
  constructor
  · cases hY.2.1
    case inr =>
      rename_i h
      subst h
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, not_forall, Classical.not_imp, false_and]
    case inl =>
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, not_forall, Classical.not_imp, and_self, true_or,
        true_and]
  ·
    simp_all
    obtain ⟨left, right⟩ := hx
    obtain ⟨left_1, right_1⟩ := hY
    obtain ⟨w, h⟩ := right
    obtain ⟨left_2, right⟩ := right_1
    obtain ⟨left_3, right_1⟩ := h
    obtain ⟨left_4, right_1⟩ := right_1
    cases left_2 with
    | inl h =>
      cases left_4 with
      | inl h_1 => simp_all only
      | inr h_2 =>
        subst h_2
        simp_all only [not_true_eq_false]
    | inr h_1 =>
      cases left_4 with
      | inl h =>
        subst h_1
        simp_all only [not_true_eq_false]
      | inr h_2 =>
        subst h_1 h_2
        simp_all only [not_false_eq_true, not_true_eq_false]
  use X
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_powerset]
    exact SF.inc_ground X SFX
  · right
    simp

noncomputable def maximal_hyperedge_subtype  (SF : ClosureSystem α) [DecidablePred SF.sets]
  (X : Finset α) (x : α) (SFX : SF.sets X) (hx : x ∈ X \ (coveringIntersection SF X)) :
  Subtype (λ Y => SF.sets Y ∧ x ∈ X \ Y ∧ cover SF Y X) :=
  let Y := Classical.choose (maximal_hyperedge_exists SF X x SFX hx)
  let h := Classical.choose_spec (maximal_hyperedge_exists SF X x SFX hx)
  ⟨Y, h⟩


def plus_condition (SF:ClosureSystem α)  [DecidablePred SF.sets]:Prop:=
  ∀ X:Finset SF.ground, SF.sets (X.image Subtype.val) → (coveringIntersection_sub SF X) ⊆ (dash SF X)

lemma abetype_theorem_lemma (SF:ClosureSystem α)  [DecidablePred SF.sets]:
   plus_condition SF → ∀ v : α, v ∈ SF.ground \ ((dash SF SF.ground.attach).image Subtype.val)
   → ∀ X:Finset α, (v ∈ X → SF.sets X
   → v ∈ X \ (coveringIntersection SF X)) :=
by
  dsimp [plus_condition]
  intro pc
  intro v hv
  intro s hs hss

  let ssub:= s.subtype (fun x => x ∈ SF.ground)
  have sg: s ⊆ SF.ground:= SF.inc_ground s hss
  have notin:v ∈ SF.ground \ ((dash SF ssub).image Subtype.val):=
  by
    rw [Finset.mem_sdiff]
    have monod: dash SF ssub ⊆ dash SF SF.ground.attach :=
    by
      have : ssub ⊆ SF.ground.attach :=
      by
        dsimp [ssub]
        intro x
        intro a
        simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
          not_exists, true_and, Finset.mem_subtype, Finset.mem_attach, ssub]
      exact monotone_dash SF ssub SF.ground.attach this

    simp
    constructor
    · simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
      not_exists, true_and, ssub]
    · rw [Finset.mem_sdiff] at hv
      intro hvv
      intro vin
      let vm := monod vin
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const,
        not_true_eq_false, and_false, vm]
      --ここまででnotinを証明。

  have :(coveringIntersection SF s) ⊆ ((dash SF ssub).image Subtype.val) :=
  by
    dsimp [ssub]
    let pcs := pc ssub
    have val_eq: Finset.image Subtype.val (Finset.subtype (fun x => x ∈ SF.ground) s) = s :=
      by
        simp_all only [forall_true_left, ssub]
        ext a : 1
        simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
          exists_eq_right_right, and_iff_left_iff_imp, ssub]
        intro a_1
        exact sg a_1
    have :SF.sets (Finset.image Subtype.val ssub) :=
    by
      dsimp [ssub]
      simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
        not_exists, true_and, exists_true_left, ssub]
    specialize pcs this
    dsimp [ssub] at pcs
    dsimp [coveringIntersection_sub] at pcs
    rw [val_eq] at pcs
    intro x hx
    have :x ∈ SF.ground :=
    by
      dsimp [coveringIntersection] at hx
      rw [mem_finsetIntersection_iff_of_nonempty] at hx
      · simp_all [ssub]
        obtain ⟨left, right⟩ := hv
        simp_all only [forall_true_left, subset_refl, ssub]
        apply sg
        simp_all only [true_and, or_true, ssub]

      · use s  -- intersectionの非空性
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_powerset]
          simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            not_exists, true_and, exists_true_left, ssub]
        · right
          rfl

    simp_all [ssub]
    simp_all only [ssub]
    obtain ⟨left, right⟩ := hv
    --obtain ⟨left_1, right_1⟩ := property
    simp_all only [forall_true_left, ssub]
    apply pcs
    simp_all only [Finset.mem_subtype, ssub]

  have notin2: v ∈ s \ (coveringIntersection SF s) :=
  by
    rw [@Finset.mem_sdiff]
    constructor
    · simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right,
      exists_eq_right, not_exists, exists_true_left, true_and, ssub]
    · intro notinv
      let nt := this notinv
      rw [Finset.mem_sdiff] at notin
      exact notin.2 nt

theorem abetype_theorem (SF:ClosureSystem α)  [DecidablePred SF.sets]:
   plus_condition SF → ∀ v : α, v ∈ SF.ground \ ((dash SF SF.ground.attach).image Subtype.val) → SF.is_rare v :=
by
  dsimp [plus_condition]
  intro pc
  intro v hv
  let S:= SF.ground.powerset.filter (fun s => SF.sets s ∧ v ∈ s)
  let T:= SF.ground.powerset.filter (fun s => SF.sets s ∧ v ∉ s)

  --sからtへの単射を作りたい。
  let ii : S → T:= fun s =>
    by
      dsimp [S] at s
      obtain ⟨val,property⟩ := s
      let ssub:= val.subtype (fun x => x ∈ SF.ground)
      rw [Finset.mem_filter] at property
      rw [Finset.mem_powerset] at property
      have sg: val ⊆ SF.ground:= property.1
      have notin:v ∈ SF.ground \ ((dash SF ssub).image Subtype.val):=
      by
        rw [Finset.mem_sdiff]
        have monod: dash SF ssub ⊆ dash SF SF.ground.attach :=
        by
          have : ssub ⊆ SF.ground.attach :=
          by
            dsimp [ssub]
            intro x
            intro a
            simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
              not_exists, true_and, Finset.mem_subtype, Finset.mem_attach, S, ssub]
          exact monotone_dash SF ssub SF.ground.attach this

        simp
        constructor
        · simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
          not_exists, true_and, S, ssub]
        · rw [Finset.mem_sdiff] at hv
          intro hvv
          intro vin
          let vm := monod vin
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const,
            not_true_eq_false, and_false, vm]
          --ここまででnotinを証明。

      have :(coveringIntersection SF val) ⊆ ((dash SF ssub).image Subtype.val) :=
      by
        dsimp [ssub]
        let pcs := pc ssub
        have val_eq: Finset.image Subtype.val (Finset.subtype (fun x => x ∈ SF.ground) val) = val :=
          by
            simp_all only [forall_true_left, S, ssub]
            ext a : 1
            simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
              exists_eq_right_right, and_iff_left_iff_imp, S, ssub]
            intro a_1
            exact sg a_1
        have :SF.sets (Finset.image Subtype.val ssub) :=
        by
          dsimp [ssub]
          simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
            not_exists, true_and, exists_true_left, S, ssub]
        specialize pcs this
        dsimp [ssub] at pcs
        dsimp [coveringIntersection_sub] at pcs
        rw [val_eq] at pcs
        intro x hx
        have :x ∈ SF.ground :=
        by
          dsimp [coveringIntersection] at hx
          rw [mem_finsetIntersection_iff_of_nonempty] at hx
          · simp_all [S, ssub]
            obtain ⟨left, right⟩ := hv
            obtain ⟨left_1, right_1⟩ := property
            simp_all only [forall_true_left, subset_refl, S, ssub]
            apply sg
            simp_all only [true_and, or_true, S, ssub]

          · use val  -- intersectionの非空性
            rw [Finset.mem_filter]
            constructor
            · rw [Finset.mem_powerset]
              simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
                not_exists, true_and, exists_true_left, S, ssub]
            · right
              rfl

        simp_all [S, ssub]
        simp_all only [S, ssub]
        obtain ⟨left, right⟩ := hv
        obtain ⟨left_1, right_1⟩ := property
        simp_all only [forall_true_left, S, ssub]
        apply pcs
        simp_all only [Finset.mem_subtype, S, ssub]

      have notin2: v ∈ val \ (coveringIntersection SF val) :=
      by
        rw [@Finset.mem_sdiff]
        constructor
        · simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
          not_exists, true_and, exists_true_left, S, ssub]
        · intro notinv
          let nt := this notinv
          rw [Finset.mem_sdiff] at notin
          exact notin.2 nt

      --tとしては、sとcover関係があるhyperedgeを持ってくる必要がある。

      let ⟨Y, hY⟩ := maximal_hyperedge_subtype SF val v property.2.1 notin2
      obtain ⟨hY1,hY2,hY3⟩ := hY
      have :SF.sets Y ∧ v ∉ Y :=
      by
        simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,not_exists, true_and, exists_true_left, not_false_eq_true, and_self, ssub]

      have hY : Y ∈ T :=
      by
        dsimp [T]
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_powerset]
          exact SF.inc_ground Y hY1
        · exact this

      exact ⟨Y,hY⟩

  --この部分ではiiが単射であることを示す。補題を利用。
  --XとYがcover関係にあることを証明する必要がある。
  have : ∀ X :S, cover SF (ii X) X:=
  by
    intro X
    dsimp [cover]
    constructor
    · have : (ii X).val ∈ T :=
      by
        exact (ii X).property
      dsimp [T] at this
      rw [Finset.mem_filter] at this
      exact this.2.1
    · constructor
      ·
        obtain ⟨val, property⟩ := X
        simp_all only [T]
        simp_all only [Finset.mem_filter, Finset.mem_powerset, S, T]
      · constructor
        · refine Finset.ssubset_iff_subset_ne.mpr ?_
          constructor
          · sorry --情報が足りない？そもそもiiが分解できない。
          · sorry --
        · intro C hC
          --show ↑(ii X) ⊆ C → ↑(ii X) ⊆ ↑X → C = ↑(ii X) ∨ C = ↑X
          sorry --補題を作った方がよい？

  --単射性をいうために、
  --lemma injective_cover (SF : ClosureSystem α) [DecidablePred SF.sets]
  -- (X1 X2 Y1 Y2 : Finset α)
  --  (c1 : cover SF Y1 X1) (c2 : cover SF Y2 X2)
  --  (hY : Y1 = Y2)
  --  (h_nonempty : ((X1 \ Y1) ∩ (X2 \ Y2)).Nonempty) : X1 = X2 := by
  -- を使う。

  --最後にiiの単射性を使って、vがrareであることを示す。補題を利用。
