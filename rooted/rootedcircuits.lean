import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Prod
import rooted.CommonDefinition
import rooted.RootedSets
import rooted.ClosureOperator
import Mathlib.Tactic
import LeanCopilot

-- 有限集合の型
variable {α : Type} [Fintype α] [DecidableEq α]

open Classical  --これでsetsのdecidablePredの問題が解決した。

-- RootedCircuits の構造の定義。RootedSetsから極小性を満たしたもの。
structure RootedCircuits (α : Type) [DecidableEq α] extends RootedSets α where
  minimality :
    ∀ p₁ p₂:(ValidPair α), p₁ ∈ rootedsets → p₂ ∈ rootedsets →
      p₁.root = p₂.root → p₁.stem ⊆ p₂.stem → p₁.stem = p₂.stem

--RootedSetsから極小なものを計算して、RootedCircuitsを構築する関数。
--circuitsに関する補題と、circuitsに関係しない補題でファイルを分けた方がいいかも。
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

    /- 対応するMathlibの定理が見つからなかったけど、ssubset_iff_subset_neが見つかった。
    have {s t : Finset α} :  s ⊆ t → s ≠ t → s ⊂ t :=
    by
      intro st snt
      apply Finset.ssubset_def.mpr
      constructor
      exact st
      by_contra hcontra
      let tmp := Finset.Subset.antisymm st hcontra
      contradiction
    -/
    have hproper : p₁.stem ⊂ p₂.stem :=
    by
      exact ssubset_iff_subset_ne.mpr ⟨hsubset, hneq⟩

    simp_all only [ne_eq]

  nonempty_ground := by
    obtain ⟨x, hx⟩ := RS
    simp_all only
}




--根つき集合が与えられたら、同じ根を持つものの中でステムが包含関係で極小なものが存在する。補題として何回か利用している。
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
  simp_all only [Finset.mem_filter, Finset.lt_eq_subset, and_imp, true_and, Fs]--
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
    simp_all only [and_true, and_self, F, Fs, v]

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
    · simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, forall_exists_index, F, Fs, v]

    · --∀ q ∈ RS.rootedsets, q.root = p₁.root → ¬q.stem ⊂ t.stem
      constructor
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, forall_exists_index, F, Fs, v]
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

      simp_all only [F]
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, forall_exists_index, F, Fs, v]

--rootedcircuits_minimalityとほぼ同じだが、rootedcircuitsの中から取れる形に書き換えた。
omit [Fintype α] in
lemma rootedcircuits_extsts (RS : RootedSets α) (p : ValidPair α) :
  p ∈ RS.rootedsets → ∃r ∈ (rootedcircuits_from_RS RS).rootedsets, r.root = p.root ∧ r.stem ⊆ p.stem :=
by
  intro hp
  simp_all only [rootedcircuits_from_RS]
  obtain ⟨r,hr⟩ := rootedcircuits_minimality RS p hp
  use r
  simp_all only [Finset.mem_filter, not_false_eq_true, implies_true, and_self]


--rootedset_setfamilyのrootedcircuits版。rootedcircuitsの中に存在することをいっている。
--rooted set版は、rootedset_setfamily。subtype版は下にある。
lemma rootedcircuits_setfamily (RS : RootedSets α) (SF:ClosureSystem α)
 (eq:  rootedsetToClosureSystem RS = SF) :
  ∀ (s : Finset α), s ⊆ SF.ground → (¬ SF.sets s ↔ ∃ (p : ValidPair α), p ∈ (rootedcircuits_from_RS RS).rootedsets ∧ p.stem ⊆ s ∧ p.root  ∈ (closureOperator SF (s.subtype (λ x => x ∈ SF.ground))).image Subtype.val ∧ p.root ∉ s) :=
by
  intro s
  intro hs
  let rss := rootedset_setfamily RS SF eq s hs
  apply Iff.intro
  · intro a
    --specialize eqsets s
    let rma := rss.mp a
    obtain ⟨p, hp⟩ := rma
    obtain ⟨q, hq⟩ := rootedcircuits_minimality RS p hp.1
    use q
    constructor
    · subst eq
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, rss]
      rw [rootedcircuits_from_RS]
      simp_all only [Finset.mem_filter, not_false_eq_true, implies_true, and_self]
    · constructor
      · let hp21 := hp.2.1
        let hq221 := hq.2.2.1
        exact hq221.trans hp21
      · constructor
        · subst eq
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, rss]
        · subst eq
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, not_false_eq_true, rss]
  · intro a
    apply rss.mpr
    obtain ⟨p, hp⟩ := a
    use p
    constructor
    · dsimp [rootedcircuits_from_RS] at hp
      subst eq
      simp_all only [Finset.mem_filter, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    · constructor
      · let hp21 := hp.2.1
        let hp22 := hp.2.2
        exact hp21
      · constructor
        exact hp.2.2.1
        exact hp.2.2.2

--rootedcircuits_setfamilyのsubtype版。
lemma rootedcircuits_setfamily_subtype (RS : RootedSets α) (SF:ClosureSystem α)
 (eq:  rootedsetToClosureSystem RS = SF) :
  ∀ (s : Finset SF.ground), (¬ SF.sets (s.image Subtype.val)  ↔ ∃ (p : ValidPair α), p ∈ (rootedcircuits_from_RS RS).rootedsets ∧ p.stem ⊆ (s.image Subtype.val) ∧ p.root  ∈ (closureOperator SF s).image Subtype.val ∧ p.root ∉ (s.image Subtype.val)) :=
by
  intro st
  let s := st.image Subtype.val
  have : s ⊆ SF.ground := by
    rw [Finset.subset_iff]
    intro x hx
    subst eq
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, s]
    obtain ⟨w, h⟩ := hx
    simp_all only
  let rsr := rootedcircuits_setfamily RS SF eq s this
  convert rsr
  subst eq
  simp_all only [s]
  ext a : 1
  simp_all only [Finset.mem_subtype, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
    Subtype.coe_eta, Finset.coe_mem, exists_const]

/-
--Mathlibにないと思って証明したが、Finset.nonempty_iff_ne_emptyを使ってNonemptyを使えば良いとClaudeに教えてもらった。
lemma Finset.exists_mem_of_ne_empty2 {α : Type} [DecidableEq α] (s : Finset α) (h : s ≠ ∅) :
  ∃ x, x ∈ s :=
by
  -- Finset の内部構造を展開
  match s with
  | ⟨val, nodup⟩ =>
  simp at h -- s ≠ ∅ を Multiset の条件に変換
  -- Multiset に要素があることを証明
  simp_all only [Finset.mem_mk]
  contrapose! h
  ext a : 1
  simp_all only [Finset.mem_mk, Finset.not_mem_empty]
-/
--結果的には、これで良かった。Nonemptyというのは、要素が存在するのと同じだった。

--rootedcircuitsを考えても、根つき集合族を考えても、集合族が同じであること。
theorem rootedcircuits_makes_same_setfamily: ∀ (RS : RootedSets α), ∀ (s : Finset α),
  (rootedsetToClosureSystem (rootedcircuits_from_RS RS).toRootedSets).sets s = (rootedsetToClosureSystem RS).sets s :=
by
  intro RS s
  simp_all
  apply Iff.intro
  · intro h
    dsimp [rootedsetToClosureSystem] at h
    dsimp [filteredFamily] at h
    simp_all
    dsimp [rootedcircuits_from_RS] at h
    by_contra hcontra --ここで背理法。sを排除するrooted circuitが存在することをいう。
    dsimp [rootedsetToClosureSystem] at hcontra
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
    dsimp [rootedsetToClosureSystem] at h
    dsimp [filteredFamily] at h
    --simp_all
    dsimp [rootedsetToClosureSystem]
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



---lemma rootedcircuits_setfamily (RS : RootedSets α) (SF:ClosureSystem α)
-- (eq:  rootedsetToClosureSystem RS = SF) :
--  ∀ (s : Finset α), s ⊆ SF.ground → (¬ SF.sets s ↔ ∃ (p : ValidPair α), p ∈ (rootedcircuits_from_RS RS).rootedsets ∧ p.stem ⊆ s ∧ p.root  ∈ (closureOperator SF (s.subtype (λ x => x ∈ SF.ground))).image Subtype.val ∧ p.root ∉ s) :=
--の系として得られる。ステムを含んで根を含まないものは、hyperedgeでないので。
