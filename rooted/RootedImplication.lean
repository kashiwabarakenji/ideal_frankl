import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Defs
import rooted.ClosureOperator
import rooted.RootedSets
import rooted.RootedCircuits
import rooted.Bridge
import LeanCopilot

variable {α : Type} [Fintype α] [DecidableEq α]

--根付き集合のimplicationの関係。pとqからrが推論される。
lemma closuresystem_rootedsets_implication (SF:ClosureSystem α)[DecidablePred SF.sets]:-- [∀ s, Decidable (SF.sets s)]:
  let RS := rootedSetsFromSetFamily SF.toSetFamily
  ∀ p ∈ RS.rootedsets, ∀ q ∈ RS.rootedsets, q.root ∈ p.stem → p.root ∉ q.stem
  → ∃ r ∈ RS.rootedsets, r.root = p.root ∧ r.stem ⊆ (p.stem ∪ q.stem) \ {q.root}  :=
by
  intro RS
  intro p
  intro hp
  intro q
  intro hq
  intro hqin
  intro hqnotin
  dsimp [RS] at hp hq
  simp_all only [RS]
  have : p.root ∉ ((p.stem ∪ q.stem) \ {q.root}) :=
  by
    simp_all only [Finset.mem_sdiff, Finset.mem_union, or_false, Finset.mem_singleton, not_and, Decidable.not_not, RS]
    intro a
    cases q
    simp_all only [RS]
    cases p
    simp_all only [RS]
  let r := ValidPair.mk ((p.stem ∪ q.stem) \ {q.root}) p.root this
  use r
  simp_all only [subset_refl, and_true, RS, r]
  dsimp [rootedSetsFromSetFamily]
  dsimp [rootedSetsSF]
  dsimp [allCompatiblePairs]
  dsimp [isCompatible]
  dsimp [allPairs]
  simp at r
  simp
  constructor
  · constructor
    · have :(p.stem ∪ q.stem)  ⊆ SF.ground:=
      by
        rw [@Finset.union_subset_iff]
        constructor
        · exact (RS.inc_ground p hp).1
        · exact (RS.inc_ground q hq).1
      refine Finset.subset_iff.mpr ?_
      intro x a
      simp_all only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, RS, r]
      obtain ⟨left, right⟩ := a
      cases left with
      | inl h =>
        apply this
        simp_all only [Finset.mem_union, true_or, RS, r]
      | inr h_1 =>
        apply this
        simp_all only [Finset.mem_union, or_true, RS, r]
    · exact (RS.inc_ground p hp).2
  · constructor
    · intro h
      cases h
      case inl h=>
        exfalso
        exact p.root_not_in_stem h
      case inr h=>
        simp_all only [not_true_eq_false, RS, r]
    · intro t
      intro sfs
      intro pq
      dsimp [rootedSetsFromSetFamily] at hp
      dsimp [rootedSetsSF] at hp
      dsimp [allCompatiblePairs] at hp
      dsimp [isCompatible] at hp
      simp at hp
      dsimp [rootedSetsFromSetFamily] at hq
      dsimp [rootedSetsSF] at hq
      dsimp [allCompatiblePairs] at hq
      dsimp [isCompatible] at hq
      simp at hq
      obtain ⟨wp1, hp⟩ := hp
      obtain ⟨wp2, hp⟩ := hp
      obtain ⟨wp3, hp⟩ := hp
      obtain ⟨wp3, wp32, wp33⟩ := wp3
      obtain ⟨wq1, hq⟩ := hq
      obtain ⟨wq2, hq⟩ := hq
      obtain ⟨wq3, hq⟩ := hq
      obtain ⟨wq3, wq32, wq33⟩ := wq3
      --pqを使う。tはq.stemを含むので、q.rootも含む。ということは、pstemを含むので、p.rootを含む。
      have : q.root ∈ t :=
      by
        have qt: q.stem ⊆ t:=
        by
          subst hp hq
          simp_all only [RS]
          rw [@Finset.subset_iff] at pq
          intro w hw
          simp_all only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, and_imp, or_true, RS]
          apply pq
          · simp_all only [or_true, RS]
          · apply Aesop.BuiltinRules.not_intro
            intro a
            subst a
            simp_all only [RS]
        have : wq1 = q.stem :=
        by
          subst hq
          simp_all only [RS]
        rw [this] at wq33
        subst hq
        exact wq33 t sfs qt

      --thisとpqを使う。
      have pt: p.stem ⊆ t :=
      by
        intro x hx
        by_cases x = q.root
        case pos =>
          rename_i h
          subst hq
          simp_all only [RS]
        case neg =>
          subst hp hq
          simp_all only [RS]
          apply pq
          simp_all only [Finset.mem_sdiff, Finset.mem_union, true_or, Finset.mem_singleton, not_false_eq_true,
            and_self, RS]
      have : wp2 = p.root :=
      by
        subst hp
        simp_all only [RS]
      rw [this] at wp33
      have : wp1 = p.stem :=
      by
        subst hp
        rfl
      rw [this] at wp33

      exact wp33 t sfs pt

lemma closuresystem_implication_stem1 (SF:ClosureSystem α)[DecidablePred SF.sets] :
  let RS := rootedSetsFromSetFamily SF.toSetFamily
  ∀ p ∈ RS.rootedsets, ∀ q ∈ RS.rootedsets, q.root ∈ p.stem → p.root ∉ q.stem
  → p.stem.card = 1 → q.stem.card = 1
  → ∃ r ∈ RS.rootedsets, r.root = p.root ∧ r.stem ⊆ p.stem ∪ q.stem \ {q.root} ∧ r.stem.card = 1 :=
by
  intro RS
  intro p
  intro hp
  intro q
  intro hq
  intro hqin
  intro hqnotin
  intro hpcard
  intro hqcard
  dsimp [RS] at hp hq
  simp_all only [RS]
  apply Exists.intro
  · apply And.intro
    on_goal 2 => apply And.intro
    on_goal 2 => rfl
    · simp_all only
    · simp_all only [Finset.subset_union_left, and_self]
