--根付きサーキットに関する定義と定理を集めた。根付き集合については、RootedSets.leanを参照。
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
variable {α : Type}  [DecidableEq α]

open Classical  --これでsetsのdecidablePredの問題が解決した。

-- RootedCircuits の構造の定義。RootedSetsから極小性を満たしたもの。
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
/--
  ルート `p₁.root` を共有し，`p₁.stem` に含まれる stem の中で
  ⊂ に関して極小な stem を与える根付き集合 `p₂` が存在する。
-/

--omit [Fintype α] in
lemma rootedcircuits_minimality
    (RS : RootedSets α) (p₁ : ValidPair α) :
    p₁ ∈ RS.rootedsets →
      ∃ p₂ ∈ RS.rootedsets,
        p₁.root = p₂.root ∧
        p₂.stem ⊆ p₁.stem ∧
        ∀ q ∈ RS.rootedsets, q.root = p₂.root → ¬ (q.stem ⊂ p₂.stem) := by
  intro hp₁

  ----------------------------------------------------------------
  -- 1.  stem の候補集合 F と，そのうち root を含まないもの Fs
  ----------------------------------------------------------------
  let F : Finset (Finset α) :=
    RS.ground.powerset.filter (λ stem =>
      ∃ p ∈ RS.rootedsets,
        p.stem = stem ∧ p.root = p₁.root ∧ stem ⊆ p₁.stem)

  let Fs : Finset (Finset α) :=
    F.filter (λ s => s ⊆ RS.ground \ {p₁.root})

  ----------------------------------------------------------------
  -- 2.  Fs が空でない（p₁.stem が入る）ことを示す
  ----------------------------------------------------------------
  have hFs_nonempty : Fs.Nonempty := by
    have h₁ : p₁.stem ⊆ RS.ground := (RS.inc_ground p₁ hp₁).1
    have h₂ : p₁.root ∉ p₁.stem := p₁.root_not_in_stem

    -- p₁.stem ∈ F
    have h_in_F : p₁.stem ∈ F := by
      simp_all only [Finset.mem_filter, Finset.mem_powerset, subset_refl, and_true, true_and, F]
      apply Exists.intro
      · apply And.intro
        on_goal 2 => apply And.intro
        on_goal 3 => {rfl
        }
        · simp_all only
        · simp_all only

    -- p₁.stem ⊆ ground \ {root}
    have h_sub_root : p₁.stem ⊆ RS.ground \ {p₁.root} := by
      intro x hx
      have hx₁ : x ∈ RS.ground := h₁ hx
      have hx₂ : x ≠ p₁.root := by
        intro h_eq; subst h_eq; exact h₂ hx
      simpa [Finset.mem_sdiff, Finset.mem_singleton] using And.intro hx₁ hx₂

    exact ⟨p₁.stem, by
      simp [Fs, h_in_F, h_sub_root]⟩

  ----------------------------------------------------------------
  -- 3.  Fs の ⊂ で極小な stem `t` を取り，その証明を `ht_min`
  ----------------------------------------------------------------
  obtain ⟨t, ht_min⟩ := Finset.exists_minimal (s := Fs) hFs_nonempty
  -- `t ∈ Fs`
  have htFs : t ∈ Fs := ht_min.1

  ----------------------------------------------------------------
  -- 4.  t ∈ Fs から情報を分解して p₂ を得る
  ----------------------------------------------------------------
  --   (1) まず Fs の filter をはずす
  obtain ⟨htF, ht_sub_root⟩ := (Finset.mem_filter).mp htFs
  --   (2) つぎに F の filter をはずす
  obtain ⟨_, ⟨p₂, hp₂, hstem, hroot, hsub⟩⟩ :=
    (Finset.mem_filter).mp htF

  have ht_eq : p₂.stem = t := by
    simpa using hstem

  ----------------------------------------------------------------
  -- 5.  目的の結論を組み立てる
  ----------------------------------------------------------------
  refine ⟨p₂, hp₂, ?_, ?_, ?_⟩

  -- (i) roots が一致
  · simp [hroot]

  -- (ii)  stem ⊆ p₁.stem
  · simpa [ht_eq] using hsub

  -- (iii)  極小性
  · intro q hq hqroot hss
    ----------------------------------------------------------------
    --  q.stem が Fs に属することを示す
    ----------------------------------------------------------------
    have hq_in_F : q.stem ∈ F := by
      have hq_sub_ground : q.stem ⊆ RS.ground := (RS.inc_ground q hq).1
      have hq_cond :
          ∃ p ∈ RS.rootedsets,
            p.stem = q.stem ∧ p.root = p₁.root ∧ q.stem ⊆ p₁.stem := by
        refine ⟨q, hq, rfl, ?_, ?_⟩
        · -- roots 一致
          simpa [hroot] using hqroot
        · -- q.stem ⊆ p₁.stem  （q.stem ⊂ p₂.stem ⊆ p₁.stem）
          have : q.stem ⊂ p₂.stem := by
            simpa [ht_eq] using hss
          rw [←hstem] at hsub
          have hss2: q.stem ⊆ p₂.stem := by
            exact subset_of_ssubset hss
          exact this.subset.trans hsub
      simp [F, hq_sub_ground, hq_cond]

    have hq_sub_root : q.stem ⊆ RS.ground \ {p₁.root} := by
      intro x hx
      have hx_ground : x ∈ RS.ground := (RS.inc_ground q hq).1 hx
      have hx_not_root : x ≠ p₁.root := by
        intro h_eq
        have : q.root = p₁.root := by simpa [hroot] using hqroot
        have : q.root ∈ q.stem := by
          have : x = q.root := by
            subst ht_eq h_eq
            simp_all only [Finset.mem_filter, Finset.mem_powerset, and_true, true_and, and_self, F, Fs]
          rw [this] at hx
          exact hx
        exact (q.root_not_in_stem) this
      simpa [Finset.mem_sdiff, Finset.mem_singleton] using And.intro hx_ground hx_not_root

    have hq_in_Fs : q.stem ∈ Fs := by
      simp [Fs, hq_in_F, hq_sub_root]

    ----------------------------------------------------------------
    --  q.stem ⊂ t は Minimal 性に反する
    ----------------------------------------------------------------
    have hlt : (q.stem : Finset α) < t := by
      -- `Finset.lt_eq_subset` で < ↔ ⊂
      simpa [Finset.lt_eq_subset, ht_eq] using hss

    have hlt2: q.stem ≤ t := by
      exact le_of_lt hlt
    let h_cont := ht_min.2 hq_in_Fs hlt2
    have htl3: t < t := by
      exact lt_of_le_of_lt h_cont hlt
    rw [Finset.lt_iff_ssubset] at htl3
    obtain ⟨h_subset, h_ne⟩ := htl3
    exact h_ne h_subset


--rootedcircuits_minimalityとほぼ同じだが、rootedcircuitsの中から取れる形に書き換えた。
--omit [Fintype α] in
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
lemma rootedcircuits_setfamily [Fintype α]  (RS : RootedSets α) (SF:ClosureSystem α)
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
lemma rootedcircuits_setfamily_subtype [Fintype α] (RS : RootedSets α) (SF:ClosureSystem α)
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


--rootedcircuitsを考えても、根つき集合族を考えても、集合族が同じであること。
theorem rootedcircuits_makes_same_setfamily[Fintype α]:  ∀ (RS : RootedSets α), ∀ (s : Finset α),
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
