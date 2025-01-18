import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
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
      dsimp [allPairs] at left
      rw [Finset.product] at left
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

--根つき集合が与えられたら、同じ根を持つものの中でステムが包含関係で極小なものが存在する。
omit [Fintype α] in
lemma rootedcircuits_minimality (RS : RootedSets α) (p₁:(ValidPair α)):
  p₁ ∈ RS.rootedsets → ∃ p₂ ∈ RS.rootedsets , p₁.root = p₂.root ∧   p₂.stem ⊆ p₁.stem  ∧
  ∀ q ∈ RS.rootedsets, q.root = p₂.root → ¬(q.stem ⊂ p₂.stem) :=
 by
  intro hp₁
  -- F の中で s の部分集合を考える
  let F := RS.ground.powerset.filter (λ stem => ∃ p ∈ RS.rootedsets, p.stem = stem ∧ p.root = p₁.root ∧ stem ⊆ p₁.stem)
  let Fs := F.filter (· ⊆ RS.ground \ {p₁.root})
  -- Fs が空でないことを示す
  have hFs_nonempty : Fs.Nonempty := by
    simp_all only [Fs]
    rw [Finset.filter_nonempty_iff]
    use p₁.stem
    constructor
    · dsimp [F]
      simp
      constructor
      ·exact (RS.inc_ground p₁ hp₁).1

      · apply Exists.intro
        · apply And.intro
          on_goal 2 => apply And.intro
          on_goal 3 => {rfl
          }
          · simp_all only
          · simp_all only
    · --goal p₁.stem ⊆ RS.ground \ {p₁.root}
      have pground: p₁.stem ⊆ RS.ground := by
        exact (RS.inc_ground p₁ hp₁).1
      have pr: p₁.root ∉ p₁.stem := by
        exact p₁.root_not_in_stem
      intro x hx
      simp_all only [Finset.mem_sdiff, Finset.mem_singleton]
      apply And.intro
      · exact pground hx
      · apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [not_true_eq_false]

  -- Fs は有限集合なので、極小要素が存在する
  obtain ⟨t, htFs, ht_minimal⟩ := Finset.exists_minimal Fs hFs_nonempty
  -- t が Fs に属することより t ⊆ s と t ∈ F を確認
  rw [Finset.mem_filter] at htFs
  obtain ⟨htF, hts⟩ := htFs
  -- 結果を構成
  let v: ValidPair α := {stem := t, root := p₁.root, root_not_in_stem := (by
    --Fの定義からわかるはず。
    dsimp [F] at htF
    rw [Finset.mem_filter] at htF
    rw [Finset.mem_powerset] at htF
    obtain ⟨htF, htF2⟩ := htF
    obtain ⟨htF, htF3⟩ := htF2
    have : p₁.root ∉ t := by
      rw [Finset.subset_sdiff] at hts
      simp_all only [Finset.disjoint_singleton_right,not_false_eq_true]--
    exact this
    ) }
  --ht_minimal : ∀ x ∈ Fs, ¬x < t これは包含関係。後ろで使っている。
  use v --ここでは極小なstemのものを使っている。
  simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.lt_eq_subset, and_imp, true_and, Fs, v]
  apply And.intro
  · dsimp [RootedSets.rootedsets]
    simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, forall_exists_index, F]
    --{ stem := t, root := p₁.root, root_not_in_stem := ⋯ } ∈ RS.rootedsets
    dsimp [F] at htF
    rw [Finset.mem_filter] at htF
    simp_all only [Finset.mem_powerset]
    obtain ⟨left, right⟩ := htF
    obtain ⟨w, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    obtain ⟨left_2, right⟩ := right
    subst left_2
    rw [Finset.mem_filter] at htF
    have :{ stem := w.stem, root := w.root, root_not_in_stem := w.root_not_in_stem } ∈ RS.rootedsets := by
      exact left_1
    simp_all only [Finset.mem_powerset, true_and]

  · have tp: t ⊆ p₁.stem:= by
      have : t ∈ F := by
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
      dsimp [F] at this
      rw [Finset.mem_filter] at this
      obtain ⟨left, right⟩ := this
      obtain ⟨w, h⟩ := right
      obtain ⟨left_1, right⟩ := h
      obtain ⟨left_2, right⟩ := right
      subst left_2
      simp_all only [Finset.mem_powerset]
    apply And.intro
    · exact tp

    · --∀ q ∈ RS.rootedsets, q.root = p₁.root → ¬q.stem ⊂ t.stem
      intro q a a_1
      intro qt_contra
      have hq_minimal := ht_minimal q.stem (by
        dsimp [F]
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_powerset]
          exact (RS.inc_ground q a).1

        · simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, forall_exists_index, F]
          use q
          constructor
          · exact a
          · constructor
            · rfl
            · constructor
              · exact a_1
              · --q.stem ⊆ p₁.stem
                rw [Finset.ssubset_iff_subset_ne] at qt_contra
                -- q ⊆ t を取り出す
                exact qt_contra.1.trans tp
      )
      have hq_subset : q.stem ⊆ RS.ground \ {p₁.root} := by
        rw [Finset.subset_sdiff]
        constructor
        · exact (RS.inc_ground q a).1
        · rw [←a_1]
          have : q.root ∉ q.stem := by
            exact q.root_not_in_stem
          simp_all only [Finset.disjoint_singleton_right, not_false_eq_true]--

      simp_all only [ and_imp, forall_exists_index, forall_const,
        not_false_eq_true, F]

--台集合に入っているかを考慮した方がよいかも。
lemma rootedcircuits_setfamily (RS : RootedSets α) (SF:ClosureSystem α)
  --(eq:  ∀ (s : Finset α),(filteredSetFamily_closed_under_intersection RS).sets s ↔ (SF.sets s)) :
 (eq:  filteredSetFamily_closed_under_intersection RS = SF) :
  ∀ (s : Finset α), s ⊆ SF.ground → (¬ SF.sets s ↔ ∃ (p : ValidPair α), p ∈ (rootedcircuits_from_RS RS).rootedsets ∧ p.stem ⊆ s ∧ p.root ∉ s) :=
by
  have eqsets: ∀ (s : Finset α), (filteredSetFamily_closed_under_intersection RS).sets s ↔ (SF.sets s) :=
  by
    intro s
    subst eq
    simp_all only
  have eqground: RS.ground = SF.ground :=
  by
    subst eq
    simp_all only
    simp_all only [implies_true]
    rfl
  intro s
  intro hs
  dsimp [filteredSetFamily_closed_under_intersection] at eqsets
  dsimp [filteredFamily] at eqsets
  dsimp [rootedcircuits_from_RS]
  simp_all only [not_and, Decidable.not_not, Finset.mem_filter, Finset.mem_powerset]
  apply Iff.intro
  · intro a
    specialize eqsets s
    rw [←eqsets] at a
    push_neg at a
    let ahs := a hs
    obtain ⟨p, hp⟩ := ahs
    obtain ⟨q, hq⟩ := rootedcircuits_minimality RS p hp.1
    use q  --極小な要素を使う。
    constructor
    constructor
    · exact hq.1
    · intro r hr
      intro pr
      subst eq
      simp_all only [true_and, forall_const, not_false_eq_true]
    ·
      subst eq
      simp_all only [true_and, forall_const, not_false_eq_true, and_true]
      obtain ⟨left, right⟩ := hp
      obtain ⟨left_1, right_1⟩ := hq
      obtain ⟨w, h⟩ := a
      obtain ⟨left_2, right⟩ := right
      obtain ⟨left_3, right_1⟩ := right_1
      obtain ⟨left_4, right_2⟩ := h
      obtain ⟨left_5, right_1⟩ := right_1
      obtain ⟨left_6, right_2⟩ := right_2
      intro q' hq'
      apply left_2
      exact left_5 hq'

  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    obtain ⟨left, right_1⟩ := left
    obtain ⟨left_1, right⟩ := right
    apply Aesop.BuiltinRules.not_intro
    intro a
    --eqsetsの記述と、left_1 rightの記述が矛盾しているのでは。
    let eqsetss := (eqsets s).mpr a
    let eqsetss2 := eqsetss.2 w left left_1
    contradiction

theorem rootedcircuits_makes_same_setfamily: ∀ (RS : RootedSets α), ∀ (s : Finset α),
  (filteredSetFamily_closed_under_intersection (rootedcircuits_from_RS RS).toRootedSets).sets s = (filteredSetFamily_closed_under_intersection RS).sets s :=
by
  intro RS s
  simp_all
  apply Iff.intro
  · intro h
    dsimp [filteredSetFamily_closed_under_intersection] at h
    dsimp [filteredFamily] at h
    simp_all
    dsimp [rootedcircuits_from_RS] at h
    by_contra hcontra --ここで背理法。sを排除するrooted circuitが存在することをいう。
    dsimp [filteredSetFamily_closed_under_intersection] at hcontra
    dsimp [filteredFamily] at hcontra
    have : ∃ rs ∈ RS.rootedsets , rs.stem ⊆ s ∧ rs.root ∉ s := by
      simp_all

    obtain ⟨rs, hrs⟩ := this
    let h2:= h.2
    --stem極小なものをrcとする。
    obtain ⟨rc,hrc⟩ := rootedcircuits_minimality RS rs hrs.1
    have rcs_root: rc.root = rs.root := by
      simp_all only [not_and, Decidable.not_not, Finset.mem_filter, Finset.mem_powerset, true_and, not_forall,
        Classical.not_imp, not_false_eq_true, implies_true, and_self]
    let hr := h2 rc --極小なものでそのようなものが取れることを示す。
    rw [Finset.mem_filter] at hr
    have prem: (rc ∈ RS.rootedsets ∧ ∀ q ∈ RS.rootedsets, q.root = rc.root → ¬q.stem ⊂ rc.stem) := by
      constructor
      · exact hrc.1
      · exact hrc.2.2.2
    have arg: rc.stem ⊆ s := by
      exact hrc.2.2.1.trans hrs.2.1

    let hpa := (hr prem arg) --rc.root ∈ s
    let hrs22 := hrs.2.2
    rw [rcs_root] at hpa
    contradiction

  · intro h
    dsimp [filteredSetFamily_closed_under_intersection] at h
    dsimp [filteredFamily] at h
    --simp_all
    dsimp [filteredSetFamily_closed_under_intersection]
    dsimp [filteredFamily]
    simp_all only [not_and, Decidable.not_not, Finset.mem_filter, Finset.mem_powerset]
    obtain ⟨left, right⟩ := h
    apply And.intro
    · exact left
    · intro p a a_1
      apply right
      · rw [rootedcircuits_from_RS] at a
        simp_all only [Finset.mem_filter]
      · simp_all only
