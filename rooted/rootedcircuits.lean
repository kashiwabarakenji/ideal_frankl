import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Prod
import LeanCopilot

-- 有限集合の型
variable {α : Type} [Fintype α] [DecidableEq α]

open Classical  --これでsetsのdecidablePredの問題が解決した。

structure SetFamily (α : Type) where --[DecidableEq α]  where DecidableEqをつけると、別のところで、synthesized type classエラー
  (ground : Finset α)
  (sets : Finset α → Prop)
  (inc_ground : ∀ s, sets s → s ⊆ ground)
  (nonempty_ground : ground.Nonempty)
  --[decidableSets : DecidablePred sets]
  --[fintype_ground : Fintype ground]

  --instance (SF : SetFamily α) : DecidablePred SF.sets :=
--  classical.dec_pred _

structure ClosureSystem (α : Type) [DecidableEq α]  [Fintype α] extends SetFamily α where
  (intersection_closed : ∀ s t , sets s → sets t → sets (s ∩ t))
  (has_ground : sets ground)

-- ValidPair の定義: ステム A と根 a
structure ValidPair (α : Type) where
  stem : Finset α
  root : α
  root_not_in_stem : root ∉ stem

noncomputable def allPairs (SF : SetFamily α) : Finset (Finset α × α) :=
  SF.ground.powerset.product SF.ground

def isValid (SF : SetFamily α) (stem : Finset α) (root : α) : Prop :=
  root ∉ stem ∧ ∀ t, SF.sets t → (stem ⊆ t → root ∈ t)

--disjointの証明付きの構造。集合族から定義される根付きサーキット。
noncomputable def allValidPairs (SF : SetFamily α) : Finset (Finset α × α) :=
  (allPairs SF).filter (λ (p : Finset α × α) =>
    isValid SF p.1 p.2
  )

--集合族から定義される根付きサーキット全体を与える関数。
noncomputable def rootedSets (SF : SetFamily α) [DecidableEq α] : Finset (ValidPair α) :=
  (allValidPairs SF).attach.image (λ ⟨p, h_p_in⟩ =>
    -- p : (Finset α × α)   -- h_p_in : p ∈ allValidPairs SF
    ValidPair.mk p.1 p.2 (by
      -- root_not_in_stem の証明
      simp only [allValidPairs, allPairs, Finset.mem_filter] at h_p_in
      exact h_p_in.2.1
    )
  )

--根付き集合族の構造。台集合つき。
structure RootedSets (α : Type) [DecidableEq α] where
  ground : Finset α
  rootedsets : Finset (ValidPair α)
  inc_ground : ∀ p ∈ rootedsets, p.stem ⊆ ground ∧ p.root ∈ ground
  nonempty_ground : ground.Nonempty

-- RootedSetsにフィルタされた通常の集合族の定義。こちらはSetFamilyではなく、ただの集合族。
noncomputable def filteredFamily (RS : RootedSets α):
  Finset (Finset α):=
RS.ground.powerset.filter (λ B =>
    ∀ (p : ValidPair α), p ∈ RS.rootedsets → ¬(p.stem ⊆ B ∧ p.root ∉ B))

--RootedSetsにフィルタされたSetFamilyを与える定義。
noncomputable def filteredSetFamily (RS : RootedSets α):
  SetFamily α :=
{
  ground := RS.ground
  sets := fun s => s ∈ filteredFamily RS
  inc_ground :=
  by
    intro s a
    rw [filteredFamily] at a
    simp_all only [not_and, Decidable.not_not, Finset.mem_filter, Finset.mem_powerset]
  nonempty_ground := by
    obtain ⟨x, hx⟩ := RS
    simp_all only
}

-- RootedCircuits の構造の定義。RootedSetsから極少性を満たしたもの。
structure RootedCircuits (α : Type) [DecidableEq α] extends RootedSets α where
  minimality :
    ∀ p₁ p₂:(ValidPair α), p₁ ∈ rootedsets → p₂ ∈ rootedsets →
      p₁.root = p₂.root → p₁.stem ⊆ p₂.stem → p₁.stem = p₂.stem

--RootedSetsから極小なものを計算して、RootedCircuitsを構築する関数。
def rootedcircuits_from_RS (RS : RootedSets α) : RootedCircuits α :=
{
  ground := RS.ground
  rootedsets:= RS.rootedsets.filter (λ p => ∀ q ∈ RS.rootedsets, q.root = p.root → ¬(q.stem ⊂ p.stem))
  inc_ground :=
  by
    intro p a
    simp_all only [Finset.mem_filter]
    obtain ⟨left, right⟩ := a
    apply And.intro
    · exact (RS.inc_ground p left).1
    · exact (RS.inc_ground p left).2

  minimality :=
  by
    intro p₁ p₂ hp₁ hp₂
    intro hroot hsubset
    simp only [Finset.mem_filter] at hp₁ hp₂
    -- `hp₁` と `hp₂` のフィルタ条件を取得
    obtain ⟨hp₁_in_RS, hp₁_min⟩ := hp₁
    obtain ⟨hp₂_in_RS, hp₂_min⟩ := hp₂
    -- `p₁.stem ⊆ p₂.stem` を仮定している
    by_contra hneq
    -- 仮定により `p₁.stem ⊂ p₂.stem` を導出 なぜか、定理が見つからない。
    have {s t : Finset α} :  s ⊆ t → s ≠ t → s ⊂ t :=
    by
      intro st snt
      apply Finset.ssubset_def.mpr
      constructor
      exact st
      by_contra hcontra
      let tmp := Finset.Subset.antisymm st hcontra
      contradiction

    have hproper : p₁.stem ⊂ p₂.stem :=
    by
      exact this hsubset hneq

    simp_all only [ne_eq]

  nonempty_ground := by
    obtain ⟨x, hx⟩ := RS
    simp_all only
}

--filteredFamilyが共通部分について閉じていること。次の言明の補題になる。
omit [Fintype α] in
theorem filteredFamily_closed_under_intersection (RS : RootedSets α) [DecidablePred (λ p => p ∈ RS.rootedsets)]:
  ∀ B₁ B₂ : Finset α, B₁ ∈ filteredFamily RS → B₂ ∈ filteredFamily RS → (B₁ ∩ B₂) ∈ filteredFamily RS :=
by
  intros B₁ B₂ hB₁ hB₂
  simp only [filteredFamily, Finset.mem_filter] at hB₁ hB₂ ⊢
  obtain ⟨hB₁sub, hB₁cond⟩ := hB₁
  obtain ⟨hB₂sub, hB₂cond⟩ := hB₂
  have hInterSub : B₁ ∩ B₂ ⊆ RS.ground :=
  by
    simp_all only [Finset.mem_powerset, not_and, Decidable.not_not]
    intro p hp
    simp_all only [Finset.mem_inter]
    obtain ⟨left, right⟩ := hp
    exact hB₂sub right
  constructor
  simp_all only [Finset.mem_powerset, not_and, Decidable.not_not]

  intro p hp
  specialize hB₁cond p hp
  specialize hB₂cond p hp
  by_contra hContr
  simp only [Finset.subset_inter_iff, not_and, not_not] at hContr
  simp_all only [Finset.mem_powerset, true_and, Decidable.not_not, Finset.mem_inter, and_self, not_true_eq_false,
    and_false]

--RootedSetsが与えられた時に、閉集合族を与える関数
def filteredSetFamily_closed_under_intersection (RS : RootedSets α) :
  ClosureSystem α :=
{
  ground := RS.ground
  intersection_closed := filteredFamily_closed_under_intersection RS,
  has_ground := by
    simp only [filteredFamily, Finset.mem_filter]
    constructor
    simp only [Finset.mem_powerset, not_and, Decidable.not_not]
    intro p hp
    simp_all only

    intro q hq
    have : q.root ∈ RS.ground := by
      exact (RS.inc_ground q hq).2
    simp_all only [not_true_eq_false, and_false, not_false_eq_true]

  inc_ground := by
    intro p hp
    simp only [filteredFamily, Finset.mem_filter] at hp
    obtain ⟨hsub, hcond⟩ := hp
    simp_all only [Finset.mem_powerset, not_and, Decidable.not_not]

  nonempty_ground := RS.nonempty_ground
}

/- いまのところ使ってないので、けしてよいかも。
def Finset.apply_function_to_subtype {α β : Type*} [DecidableEq β] {p : α → Prop}
    (s : Finset {x // p x}) (f : α → β) : Finset β :=
  s.image (λ x => f x.val)
-/

-- SetFamily から RootedSets を構築する関数 noncomputableはつけないとエラー。
noncomputable def rootedSetsFromSetFamily (SF : SetFamily α) [DecidableEq α] [DecidablePred SF.sets][Fintype SF.ground] : RootedSets α :=
  {
    ground := SF.ground

    rootedsets := rootedSets SF

   /- 以下は、苦労して作った証明が通っているが、o1に証明を簡略化してもらって外部に出したので消してもよい。
    rootedsets := by

    -- Step 1: ground のすべての部分集合 (powerset) を列挙
      let all_stems := SF.ground.powerset

      -- Step 2: 各 stem に対し、有効な root をフィルタ
      --   条件: root ∉ stem ∧ ∀ s, SF.sets s → (s ⊆ stem → root ∈ s)

      let filter_roots_for_stem := λ (stem : Finset α) =>
        SF.ground.filter (λ root =>
          root ∉ stem ∧ ∀ s, SF.sets s → (s ⊆ stem → root ∈ s)
        )
      -- Step 3: stem と root を組み合わせて 組みを作る。
      let make_pairs := λ stem =>
        (filter_roots_for_stem stem).image (fun r => (stem, r))

      let allValidPairs :=
        all_stems.attach.biUnion (λ ⟨stem, _⟩ =>
          let pairs := make_pairs stem
          if pairs.Nonempty then pairs else ∅
        )

      have h_proof: ∀ (root:α), ∀ (stem:Finset α), (stem,root) ∈ allValidPairs → root ∉ stem :=
      by
        intro root stem a
        simp_all [allValidPairs, all_stems, make_pairs, filter_roots_for_stem]
        obtain ⟨w, h⟩ := a
        obtain ⟨w_1, h⟩ := h
        apply Aesop.BuiltinRules.not_intro
        intro a
        split at h
        next h_1 =>
          simp_all only [Finset.mem_image, Finset.mem_filter, Prod.mk.injEq, exists_eq_right_right]
          simp_all only
          obtain ⟨left, right⟩ := h
          obtain ⟨left, right_1⟩ := left
          obtain ⟨left_1, right_1⟩ := right_1
          subst right
          simp_all only [not_true_eq_false]
        next h_1 => simp_all only [Finset.not_nonempty_iff_eq_empty, Finset.not_mem_empty]

      -- allValidPairs から ValidPair を構築。attachを利用。
      let validPairsProof : Finset (ValidPair α) :=
        allValidPairs.attach.image (λ vp =>
          ValidPair.mk vp.val.1 vp.val.2 (by
            have : ⟨vp.val.1, vp.val.2⟩ ∈ allValidPairs := by
              exact vp.property
            exact h_proof vp.val.2 vp.val.1 this
          )
        )
      -- 最後に Finset (ValidPair α) を返す
      exact validPairsProof,
    -/

    inc_ground := by
      intro p pa
      dsimp [rootedSets] at pa
      dsimp [allValidPairs] at pa
      simp_all --必要
      obtain ⟨w, h⟩ := pa
      obtain ⟨w_1, h⟩ := h
      obtain ⟨h2, h⟩ := h
      obtain ⟨left, right⟩ := h2
      subst h
      --simp_all only
      --dsimp [isValid] at right
      dsimp [allPairs] at left
      rw [Finset.product] at left
      --simp at left
      set wp :=  (w, w_1)
      let fmp := @Finset.mem_product _ _ SF.ground.powerset SF.ground wp --なぜか直接rwできなかった。
      have :wp.1 ∈ SF.ground.powerset ∧ wp.2 ∈ SF.ground  :=
      by
        exact fmp.mp left
      rw [Finset.mem_powerset] at this
      dsimp [wp] at this
      exact this

    nonempty_ground := SF.nonempty_ground
  }

--sがhyperedgeであるときには、sにステムが含まれて、sの外にrootがあるような根付きサーキットはない。
--rootedSetsFromSetFamilyのrooted setの定義をもっと簡単にしたほうがよい。
lemma ClosureSystemLemma  (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  ∀ s : Finset α, SF.sets s → rc ∈(rootedSetsFromSetFamily SF.toSetFamily).rootedsets
  → rc.stem ⊆ s → rc.root ∈ s :=
by
  intro s a a_1 a_2
  dsimp [rootedSetsFromSetFamily] at a_1
  dsimp [rootedSets] at a_1
  dsimp [allValidPairs] at a_1
  rw [Finset.mem_image] at a_1
  obtain ⟨w, h⟩ := a_1
  obtain ⟨val, property⟩ := w
  obtain ⟨fst, snd⟩ := val
  obtain ⟨left, right⟩ := h
  subst right
  simp_all only
  dsimp [isValid] at property
  dsimp [allPairs] at property
  have pro1:snd ∉ fst := by
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    simp [a_1, a_2] at property
  have pro2 :∀ (t : Finset α), SF.sets t → fst ⊆ SF.ground → fst ⊆ t  → snd ∈ t :=
  by
    intro t _ _ _
    dsimp [Finset.product] at property
    simp at property
    simp_all only [not_false_eq_true]

  have pro3: fst ⊆ SF.ground :=
  by
    --dsimp [Finset.product] at property
    --simp at property
    --simp_all only [not_false_eq_true, implies_true]
    --obtain ⟨left_1, right⟩ := property
    --obtain ⟨left_2, right⟩ := right
    have: s ⊆ SF.ground := by
      exact SF.inc_ground s a
    tauto

  apply pro2 s a pro3 a_2

theorem ClosureSystemTheorem (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  ∀ s : Finset α, SF.sets s → (filteredSetFamily_closed_under_intersection (rootedSetsFromSetFamily SF.toSetFamily)).sets s :=
  by
    intro s hs
    dsimp [filteredSetFamily_closed_under_intersection, rootedSetsFromSetFamily]
    dsimp [filteredFamily]
    simp_all

    constructor
    · intro p hp
      have : p ∈ SF.ground :=
      by
        have :s ⊆ SF.ground := by
          exact SF.inc_ground s hs
        exact this hp
      exact this

    · dsimp [rootedSetsFromSetFamily]
      dsimp [rootedSets]
      dsimp [allValidPairs]
      intro p hp
      apply ClosureSystemLemma SF
      exact hs --なぜか上にもってこれない。
      exact hp
