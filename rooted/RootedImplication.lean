import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Defs
import rooted.rootedcircuits
import LeanCopilot

variable {α : Type} [Fintype α] [DecidableEq α]

--根付き集合のimplicationの関係。pとqからrが推論される。
lemma closuresystem_rootedcircuits_implication (SF:ClosureSystem α)[DecidablePred SF.sets]:-- [∀ s, Decidable (SF.sets s)]:
  let RS := rootedSetsFromSetFamily SF.toSetFamily
  ∀ p ∈ RS.rootedsets, ∀ q ∈ RS.rootedsets, q.root ∈ p.stem → p.root ∉ q.stem
  → ∃ r ∈ RS.rootedsets, r.root = p.root ∧ r.stem ⊆ p.stem ∪ q.stem \ {q.root}  :=
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
  apply Exists.intro
  · apply And.intro
    on_goal 2 => apply And.intro
    on_goal 2 => {rfl
    }
    · simp_all only
    · simp_all only [Finset.subset_union_left]

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

--xとyは異なるとして、parallelを定義したほうがよい？
def parallel (SF:ClosureSystem α)[DecidablePred SF.sets] (x y:α) : Prop :=
  x ∈ SF.ground ∧ x ≠ y ∧ ∀ s : Finset α, SF.sets s → (x ∈ s ↔ y ∈ s)

lemma closuresystem_parallel_stem1 (SF:ClosureSystem α)[DecidablePred SF.sets] :
 let RS := rootedSetsFromSetFamily SF.toSetFamily
 ∀ (x y:α), parallel SF x y → x ≠ y → ∃ p ∈ RS.rootedsets, ∃ q ∈ RS.rootedsets, p.root = x ∧ q.root = y ∧ p.stem.card = 1 ∧ q.stem.card = 1 :=
by
  intro RS
  intro x
  intro y
  intro h
  intro xneqy
  dsimp [parallel] at h
  obtain ⟨hx, hxy, hxy'⟩ := h
  · dsimp [RS]
    have xnotiny: x ∉ ({y} : Finset α) := by
      intro h
      simp_all only [not_false_eq_true, true_and, ne_eq, Finset.mem_singleton]
    have yinground: y ∈ SF.ground := by
      simp_all only [hx, Finset.mem_singleton]
      have :SF.sets SF.ground := by
        exact SF.has_ground
      exact (hxy' SF.ground this).mp hx

    have :(({y} : Finset α),x) ∈ allCompatiblePairs SF.toSetFamily :=
      by
        dsimp [allCompatiblePairs]
        simp
        simp_all only [ne_eq, not_false_eq_true, Finset.mem_singleton]
        apply And.intro
        · dsimp [allPairs]
          dsimp [Finset.product]
          simp
          apply Finset.mem_product.mpr
          simp
          constructor
          · simp_all only [Finset.mem_singleton] --yinground
          · simp_all only [Finset.mem_singleton]
        · dsimp [isCompatible]
          simp_all only [Finset.mem_singleton, not_false_eq_true, Finset.singleton_subset_iff, implies_true, and_self]
    let vpy := ValidPair.mk {y} x xnotiny
    use vpy
    constructor
    · dsimp [rootedSetsFromSetFamily]
      dsimp [rootedSetsSF]
      simp
      use {y}
      use x
      simp_all only [ne_eq, not_false_eq_true, exists_const, vpy]
    · have ynotinx: y ∉ ({x} : Finset α) := by
        intro h
        simp_all only [not_false_eq_true, true_and, ne_eq, Finset.mem_singleton, implies_true, and_true,
          not_true_eq_false]
      let vpx := ValidPair.mk {x} y ynotinx
      use vpx
      constructor
      · dsimp [rootedSetsFromSetFamily]
        dsimp [rootedSetsSF]
        simp
        use {x}
        use y
        simp_all only [ne_eq, not_false_eq_true, exists_const, vpx]
        simp_all only [exists_prop, and_true]
        dsimp [allCompatiblePairs]
        dsimp [allPairs]
        dsimp [Finset.product]
        simp
        constructor
        · apply Finset.mem_product.mpr
          simp
          constructor
          · simp_all only [Finset.mem_singleton]
          · simp_all only [Finset.mem_singleton]
        · dsimp [isCompatible]
          simp_all only [Finset.mem_singleton, not_false_eq_true, Finset.singleton_subset_iff, implies_true, and_self]
      · simp_all only [not_false_eq_true, true_and, ne_eq, Finset.card_singleton, and_self]
