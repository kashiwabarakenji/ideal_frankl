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

--サイズ1の根つき集合を与える関数。
noncomputable def root_vertices_sizeone (SF: ClosureSystem α)[DecidablePred SF.sets] (s: Finset SF.ground) : Finset SF.ground :=
  let RS := rootedSetsFromSetFamily SF.toSetFamily
(SF.ground.filter (fun x  => x ∈ (s.image Subtype.val) ∧ ∃ (r : ValidPair α), r ∈ RS.rootedsets ∧ r.root = x ∧ r.stem ⊆ s.image Subtype.val)).subtype (fun x => x ∈ SF.ground)

--安部の論文に出てくるダッシュの作用素。サイズ1の根の集合のclosure。
noncomputable def dash (SF: ClosureSystem α)[DecidablePred SF.sets]  (s: Finset SF.ground) : Finset SF.ground :=
closureOperator SF (root_vertices_sizeone SF s )

--hyperege全体が包含関係で作る束のなかで、coverの関係の定義
noncomputable def cover (SF: ClosureSystem α)[DecidablePred SF.sets]  (A B : Finset α) : Prop := SF.sets A ∧ SF.sets B ∧ A ⊂ B ∧ (∀ C :Finset α, SF.sets C → A ⊆ C → A ⊆ B → C = A ∨ C = B)

-- `B` をカバーする `A` すべての共通部分を求める関数 -/
noncomputable def coveringIntersection {α : Type} [DecidableEq α] [Fintype α] (SF: ClosureSystem α)[DecidablePred SF.sets] (B : Finset α): Finset α :=
  finsetIntersection ((SF.ground.powerset.filter (fun s => (SF.sets s ∧ (cover SF s B)) ∨ s = B)))

-- coveringIntersectionの引数として、subtypeを取れるようにしたもの。値もsubtype
noncomputable def coveringIntersection_sub {α : Type} [DecidableEq α] [Fintype α]  [Fintype α] (SF: ClosureSystem α) [DecidablePred SF.sets] (B : Finset SF.ground): Finset SF.ground :=
  (@coveringIntersection α _ _ SF _ (B.image Subtype.val)).subtype (fun x => x ∈ SF.ground)

--Xに含まれるsize 1の根つき集合の根の集合 root_vertices_sizeone Xは、包含関係に関して単調。
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

/--
`injective_cover`:
  閉包系 SF において、`cover SF Y1 X1` と `cover SF Y2 X2` が成立し
  さらに `Y1 = Y2` かつ `(X1 \ Y1) ∩ (X2 \ Y2)` が空でないならば、
  `X1 = X2` となることを示す。Y1とY2は等しいのでYとして統一した。
-/
lemma injective_cover (SF : ClosureSystem α) [DecidablePred SF.sets]
    (X1 X2 Y : Finset α)
    (c1 : cover SF Y X1) (c2 : cover SF Y X2)
    (h_nonempty : ((X1 \ Y) ∩ (X2 \ Y)).Nonempty) : X1 = X2 :=
by

  /- `c1`, `c2` から被覆の成分を取り出す -/
  obtain ⟨hY1, hX1, hY1_ss_X1, cover_cond1⟩ := c1
  obtain ⟨hY1', hX2, hY1_ss_X2, cover_cond2⟩ := c2

  /- SF の交叉閉性： X1 ∩ X2 も SF.sets に属する -/
  have h_inter : SF.sets (X1 ∩ X2) := SF.intersection_closed X1 X2 hX1 hX2

  have hY1_sub_inter : Y ⊆ X1 ∩ X2 := by
    rw [@Finset.subset_inter_iff]
    constructor
    rw [Finset.ssubset_def] at hY1_ss_X1
    exact hY1_ss_X1.1

    rw [Finset.ssubset_def] at hY1_ss_X2
    exact subset_of_ssubset hY1_ss_X2

  /- X1 ∩ X2 ⊆ X1, X1 ∩ X2 ⊆ X2 は自明 -/
  have h_inter_sub_X1 : X1 ∩ X2 ⊆ X1 := by
    simp_all only [Finset.inter_subset_left]
  have h_inter_sub_X2 : X1 ∩ X2 ⊆ X2 := by
    simp_all only [Finset.inter_subset_left, Finset.inter_subset_right]

  obtain ⟨x, hx⟩ := h_nonempty
  have hx_in_X1X2 : x ∈ X1 ∩ X2 := by
    simp_all only [Finset.inter_subset_left, Finset.inter_subset_right, Finset.mem_inter, Finset.mem_sdiff, and_self]
  have hx_not_in_Y1 : x ∉ Y := by
    simp_all only [Finset.inter_subset_left, Finset.inter_subset_right, Finset.mem_inter, Finset.mem_sdiff, true_and,
      and_self, not_false_eq_true]

  have h_diff : X1 ∩ X2 ≠ Y := fun h_eq => by
    rw [← h_eq] at hx_not_in_Y1
    simp_all only [Finset.inter_subset_left, Finset.inter_subset_right]

  have cover_res1 : X1 ∩ X2 = Y ∨ X1 ∩ X2 = X1 :=
  by
    apply cover_cond1 (X1 ∩ X2) h_inter hY1_sub_inter
    simp_all only [Finset.inter_subset_left, Finset.inter_subset_right, Finset.mem_inter, ne_eq, Finset.mem_sdiff,
      not_false_eq_true, and_self]
    intro y hy
    exact hY1_ss_X1.1 hy

  /- 場合分け -/
  cases cover_res1 with
  | inl eq_to_Y1 =>
    contradiction
  | inr eq_to_X1 =>
    have h_X1_sub_X2 : X1 ⊆ X2 := by
      rw [← eq_to_X1]
      simp_all only [subset_refl, ne_eq, Finset.inter_eq_left, Finset.mem_inter, Finset.mem_sdiff, not_false_eq_true,
        and_self, and_true, true_and, Finset.inter_subset_right]

    have cover_res2 : X1 ∩ X2 = Y ∨ X1 ∩ X2 = X2 :=
    by
      apply cover_cond2 (X1 ∩ X2) h_inter hY1_sub_inter
      simp_all only [subset_refl, ne_eq, Finset.inter_eq_left, Finset.mem_inter, Finset.mem_sdiff, not_false_eq_true,
        and_self, and_true, true_and, forall_const]
      exact hY1_sub_inter.trans h_X1_sub_X2

    cases cover_res2 with
    | inl eq_to_Y1' =>
      contradiction
    | inr eq_to_X2 =>
      have h_X2_sub_X1 : X2 ⊆ X1 := by
        rw [← eq_to_X2]
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
  · simp_all
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

--ここでのsubtypeの意味は、定義域がsubtypeでなく、値がsubtype。
--証明方法を改善したので、結果的に使わなくなったが置いておく。
noncomputable def maximal_hyperedge_subtype  (SF : ClosureSystem α) [DecidablePred SF.sets]
  (X : Finset α) (x : α) (SFX : SF.sets X) (hx : x ∈ X \ (coveringIntersection SF X)) :
  Subtype (λ Y => SF.sets Y ∧ x ∈ X \ Y ∧ cover SF Y X) :=
  let Y := Classical.choose (maximal_hyperedge_exists SF X x SFX hx)
  let h := Classical.choose_spec (maximal_hyperedge_exists SF X x SFX hx)
  ⟨Y, h⟩

def plus_condition (SF:ClosureSystem α)  [DecidablePred SF.sets]:Prop:=
  ∀ X:Finset SF.ground, SF.sets (X.image Subtype.val) → (coveringIntersection_sub SF X) ⊆ (dash SF X)

--メインの定理から証明を分離。
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
  exact notin2

theorem abetype_theorem (SF:ClosureSystem α)  [DecidablePred SF.sets]:
   plus_condition SF → ∀ v : α, v ∈ SF.ground \ ((dash SF SF.ground.attach).image Subtype.val) → SF.is_rare v :=
by
  dsimp [plus_condition]
  intro pc
  intro v hv
  let S:= SF.ground.powerset.filter (fun s => SF.sets s ∧ v ∈ s)
  let T:= SF.ground.powerset.filter (fun s => SF.sets s ∧ v ∉ s)

  --SからTへの単射を作りたい。単射を作るより前に満たすべき性質を定義して、それを満たすtが非空であることをまず証明する方針。満たすべき性質とは、sの要素とtの要素は、coverの関係にあるというもの。
  have nonemp: ∀ s :S, ∃ t:T, cover SF t s :=
  by
    intro s
    dsimp [S] at s
    obtain ⟨val,property⟩ := s
    rw [Finset.mem_filter] at property
    have notin2: v ∈ val \ (coveringIntersection SF val) :=
    by
      exact abetype_theorem_lemma SF pc v hv val property.2.2 property.2.1

    --tとしては、sとcover関係があるhyperedgeを持ってくる必要がある。
    let ⟨t, hY⟩ := maximal_hyperedge_subtype SF val v property.2.1 notin2
    obtain ⟨hY1,hY2,hY3⟩ := hY
    have :SF.sets t ∧ v ∉ t :=
    by
      simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,not_exists, true_and, exists_true_left, not_false_eq_true, and_self]

    have hY : t ∈ T :=
    by
      dsimp [T]
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
        exact SF.inc_ground t hY1
      · exact this

    use ⟨t,hY⟩

  let ii:S → T:= fun s => Classical.choose (nonemp s)

  have i_prop: ∀ s:S, cover SF (ii s) s := by
    intro s
    exact Classical.choose_spec (nonemp s)

  --単射性をいうために、
  --lemma injective_cover (SF : ClosureSystem α) [DecidablePred SF.sets]
  -- (X1 X2 Y : Finset α)
  --  (c1 : cover SF Y X1) (c2 : cover SF Y X2)
  --  (h_nonempty : ((X1 \ Y1) ∩ (X2 \ Y2)).Nonempty) : X1 = X2 := by
  -- を使う。

  have inj: ∀ x1 x2 :S, ii x1 = ii x2 → x1 = x2 :=
  by
    intro x1 x2
    have c1: cover SF (ii x1) x1 :=
    by
      simp_all [T, S, ii]
      obtain ⟨val, property⟩ := x1
      simp_all only [Finset.mem_filter, Finset.mem_powerset, forall_true_left, T, S]
      apply i_prop
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, T, S]
    have c2: cover SF (ii x2) x2 :=
    by
      simp_all [T, ii, S]
      obtain ⟨val_1, property_1⟩ := x2
      simp_all only [forall_true_left, T, ii, S]
      apply i_prop
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, T, ii, S]
    intro h12
    rw [←h12] at c2
    let ic := injective_cover SF x1 x2 (ii x1) c1 c2

    have nonemp:(x1.val \ (ii x1).val ∩ (x2.val \ (ii x1).val)).Nonempty:=
    by
      let x1p := x1.property
      dsimp [S] at x1p
      rw [Finset.mem_filter] at x1p
      let x2p := x2.property
      dsimp [S] at x2p
      rw [Finset.mem_filter] at x2p
      let ht1 := (ii x1).property
      dsimp [T] at ht1
      rw [Finset.mem_filter] at ht1
      let ht2 := (ii x2).property
      dsimp [T] at ht2
      rw [Finset.mem_filter] at ht2

      use v
      rw [@Finset.mem_inter]
      constructor
      · rw [@Finset.mem_sdiff]
        constructor
        · exact x1p.2.2
        · exact ht1.2.2
      · rw[@Finset.mem_sdiff]
        constructor
        · exact x2p.2.2
        · rw [h12]
          exact ht2.2.2
    simp_all [T, ii, S]
    obtain ⟨val, property⟩ := x1
    obtain ⟨val_1, property_1⟩ := x2
    obtain ⟨left, right⟩ := hv
    simp_all only [forall_true_left, Subtype.mk.injEq, T, ii, S]
    simp_all only [T, ii, S]
    apply ic
    simp_all only [T, ii, S]

  --最後にiiの単射性を使って、vがrareであることを示す。補題を利用。
  --lemma rare_and_card (SF: SetFamily α) [DecidablePred SF.sets] (v: α):
  --SF.is_rare v ↔ (including_hyperedges SF v).card <= (deleting_hyperedges SF v).card :=

  have S_eq: S = including_hyperedges SF.toSetFamily v :=
  by
    dsimp [S]
    dsimp [including_hyperedges]
    exact Finset.filter_congr (by simp [and_comm])
  have T_eq: T = deleting_hyperedges SF.toSetFamily v :=
  by
    dsimp [T]
    dsimp [deleting_hyperedges]
    exact Finset.filter_congr (by simp [and_comm])

  have: S.card <= T.card:=
  by
    exact Finset.card_le_card_of_injective inj

  rw [S_eq,T_eq] at this

  exact (rare_and_card SF.toSetFamily v).mpr this

--もっとも一般的な形の言明。ある頂点がどのhyperedgeに対しても「最初に」とれる場合に、rareになる。
--証明は上の言明とダブっているが、この一般的なほうを補題として利用して、上の場合を証明するのがよいと思われる形。
theorem abetype_theorem_general (SF:ClosureSystem α)  [DecidablePred SF.sets](v: SF.ground):
   (∀ X:Finset SF.ground, --SF.sets (X.image Subtype.val) →
  v ∉ (coveringIntersection_sub SF X)) → SF.is_rare v :=
by
  intro pc
  let S:= SF.ground.powerset.filter (fun s => SF.sets s ∧ v.val ∈ s)
  let T:= SF.ground.powerset.filter (fun s => SF.sets s ∧ v.val ∉ s)

  --SからTへの単射を作りたい。単射を作るより前に満たすべき性質を定義して、それを満たすtが非空であることをまず証明する方針。満たすべき性質とは、sの要素とtの要素は、coverの関係にあるというもの。
  have nonemp: ∀ s :S, ∃ t:T, cover SF t s :=
  by
    intro s
    dsimp [S] at s
    obtain ⟨val,property⟩ := s
    rw [Finset.mem_filter] at property

    have :v.val ∈ val \ coveringIntersection SF val :=
    by
      rw [Finset.mem_sdiff]
      constructor
      · simp_all only [Finset.mem_filter, and_self, Finset.mem_powerset, S]
      · let pcv := pc (val.subtype (fun x => x ∈ SF.ground))
        dsimp [coveringIntersection_sub] at pcv
        simp at pcv
        convert pcv
        simp_all only [Finset.mem_filter, and_self, Finset.mem_powerset, S]
        obtain ⟨val_1, property⟩ := v
        obtain ⟨left, right⟩ := property
        ext a : 1
        simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
          exists_eq_right_right, iff_self_and]
        intro a_1
        exact left a_1

    --tとしては、sとcover関係があるhyperedgeを持ってくる必要がある。
    let ⟨t, hY⟩ := maximal_hyperedge_subtype SF val v property.2.1 this
    obtain ⟨hY1,hY2,hY3⟩ := hY
    have :SF.sets t ∧ v.val ∉ t :=
    by
      simp_all only [Finset.mem_sdiff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,not_exists, true_and, exists_true_left, not_false_eq_true, and_self]

    have hY : t ∈ T :=
    by
      dsimp [T]
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
        exact SF.inc_ground t hY1
      · exact this

    use ⟨t,hY⟩

  let ii:S → T:= fun s => Classical.choose (nonemp s)

  have i_prop: ∀ s:S, cover SF (ii s) s := by
    intro s
    exact Classical.choose_spec (nonemp s)

  --単射性をいうために、
  --lemma injective_cover (SF : ClosureSystem α) [DecidablePred SF.sets]
  -- (X1 X2 Y : Finset α)
  --  (c1 : cover SF Y X1) (c2 : cover SF Y X2)
  --  (h_nonempty : ((X1 \ Y1) ∩ (X2 \ Y2)).Nonempty) : X1 = X2 := by
  -- を使う。

  have inj: ∀ x1 x2 :S, ii x1 = ii x2 → x1 = x2 :=
  by
    intro x1 x2
    have c1: cover SF (ii x1) x1 :=
    by
      simp_all [T, S, ii]
      obtain ⟨val, property⟩ := x1
      simp_all only [Finset.mem_filter, Finset.mem_powerset, forall_true_left, T, S]
      apply i_prop
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, T, S]
    have c2: cover SF (ii x2) x2 :=
    by
      simp_all [T, ii, S]
      obtain ⟨val_1, property_1⟩ := x2
      simp_all only [forall_true_left, T, ii, S]
      apply i_prop
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, T, ii, S]
    intro h12
    rw [←h12] at c2
    let ic := injective_cover SF x1 x2 (ii x1) c1 c2

    have nonemp:(x1.val \ (ii x1).val ∩ (x2.val \ (ii x1).val)).Nonempty:=
    by
      let x1p := x1.property
      dsimp [S] at x1p
      rw [Finset.mem_filter] at x1p
      let x2p := x2.property
      dsimp [S] at x2p
      rw [Finset.mem_filter] at x2p
      let ht1 := (ii x1).property
      dsimp [T] at ht1
      rw [Finset.mem_filter] at ht1
      let ht2 := (ii x2).property
      dsimp [T] at ht2
      rw [Finset.mem_filter] at ht2

      use v
      rw [@Finset.mem_inter]
      constructor
      · rw [@Finset.mem_sdiff]
        constructor
        · exact x1p.2.2
        · exact ht1.2.2
      · rw[@Finset.mem_sdiff]
        constructor
        · exact x2p.2.2
        · rw [h12]
          exact ht2.2.2
    simp_all [T, ii, S]
    obtain ⟨val, property⟩ := x1
    obtain ⟨val_1, property_1⟩ := x2
    simp_all only [Subtype.mk.injEq, ii, S, T]
    obtain ⟨val_2, property⟩ := v
    simp_all only
    apply ic
    simp_all only [T, ii, S]

  --最後にiiの単射性を使って、vがrareであることを示す。補題を利用。
  --lemma rare_and_card (SF: SetFamily α) [DecidablePred SF.sets] (v: α):
  --SF.is_rare v ↔ (including_hyperedges SF v).card <= (deleting_hyperedges SF v).card :=

  have S_eq: S = including_hyperedges SF.toSetFamily v :=
  by
    dsimp [S]
    dsimp [including_hyperedges]
    exact Finset.filter_congr (by simp [and_comm])
  have T_eq: T = deleting_hyperedges SF.toSetFamily v :=
  by
    dsimp [T]
    dsimp [deleting_hyperedges]
    exact Finset.filter_congr (by simp [and_comm])

  have: S.card <= T.card:=
  by
    exact Finset.card_le_card_of_injective inj

  rw [S_eq,T_eq] at this

  exact (rare_and_card SF.toSetFamily v).mpr this
