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

def vertexorder (SF:ClosureSystem α)[DecidablePred SF.sets] (x y:α) : Prop :=
  x ∈ SF.ground ∧ ∀ s : Finset α, SF.sets s → (x ∈ s → y ∈ s)

lemma vertexorderlemma (SF:ClosureSystem α)[DecidablePred SF.sets] :
  let RS := rootedSetsFromSetFamily SF.toSetFamily
  ∀ (x y:α), (vertexorder SF x y ∧ x ≠ y) ↔ ∃ p ∈ RS.rootedsets, p.root = y ∧ p.stem = {x} :=
by
  intro RS
  intro x
  intro y
  apply Iff.intro
  · intro h
    dsimp [vertexorder] at h
    obtain ⟨hx, hxy⟩ := h.left
    have ynotinx: y ∉ ({x} : Finset α) := by
      intro h
      simp_all only [implies_true, and_self, true_and, Finset.mem_singleton, not_true_eq_false]
    use ValidPair.mk {x} y ynotinx
    constructor
    · dsimp [rootedSetsFromSetFamily]
      dsimp [RS]
      dsimp [rootedSetsFromSetFamily]
      dsimp [rootedSetsSF]
      dsimp [allCompatiblePairs]
      simp
      constructor
      · dsimp [allPairs]
        dsimp [Finset.product]
        simp
        apply Finset.mem_product.mpr
        constructor
        simp_all only [implies_true, and_self, true_and, Finset.mem_singleton, Finset.mem_powerset,
          Finset.singleton_subset_iff]
        simp
        let hxyground := hxy SF.ground SF.has_ground
        simp_all only [implies_true, and_self, true_and, Finset.mem_singleton, hxyground]

      · dsimp [isCompatible]
        constructor
        simp_all only [implies_true, and_self, true_and, Finset.mem_singleton, not_false_eq_true]

        intro t a a_1
        simp_all only [implies_true, and_self, true_and, Finset.mem_singleton, Finset.singleton_subset_iff]
    · simp_all only [exists_prop, and_true]
  ·
    intro a
    simp_all only [ne_eq, RS]
    constructor
    swap
    ·
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      have :w.root ∉ w.stem := by
        exact w.root_not_in_stem
      subst left_1
      simp_all only [Finset.mem_singleton, ne_eq]
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [not_true_eq_false]
    · dsimp [vertexorder]
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      subst left_1
      apply And.intro
      · let gstem := (RS.inc_ground w left).1
        simpa [right] using gstem
      · intro s a a_1
        dsimp [rootedSetsFromSetFamily] at left
        dsimp [rootedSetsSF] at left
        dsimp [allCompatiblePairs] at left
        dsimp [allPairs] at left
        simp_all
        obtain ⟨w_1, h⟩ := left
        obtain ⟨w_2, h⟩ := h
        obtain ⟨w_3, h⟩ := h
        obtain ⟨left, right_1⟩ := w_3
        subst h right
        simp_all only
        dsimp [isCompatible] at right_1
        let right12 := right_1.2 s a
        simp_all only [Finset.singleton_subset_iff]

--順序がpreorderであることを示す。この言明には、ステムの大きさには制限がない。ただし、順序に関係するのはステム1のみ。
instance vertexorder_is_preorder (SF : ClosureSystem α) [DecidablePred SF.sets] :
  Preorder {x // x ∈ SF.ground} where
    le := fun x y => vertexorder SF x.1 y.1

    le_refl := (
    by
      intro a
      simp_all only
      obtain ⟨val, property⟩ := a
      simp_all only
      constructor
      · simp_all only
      · intro s a a_1
        simp_all only
    )

    le_trans := fun x y z hxy hyz => ⟨
      hxy.1, -- x ∈ SF.ground は推移的に成立
      fun s hs hxs => hyz.2 s hs (hxy.2 s hs hxs) -- x → y → z の推移性を保証
    ⟩

def vertex_equiv (SF:ClosureSystem α)[DecidablePred SF.sets] : {x // x ∈ SF.ground} → {x // x ∈ SF.ground} → Prop :=
  fun x y => vertexorder SF x y ∧ vertexorder SF y x

-- Preorder構造のある型での例
lemma vetex_equiv_is_equivalence (SF:ClosureSystem α)[DecidablePred SF.sets]:
  Equivalence (vertex_equiv SF) :=
{
  -- 反射性: x ∼ x
  refl := fun x => by
    dsimp [vertex_equiv]
    simp
    dsimp [vertexorder]
    constructor
    simp_all only [Finset.coe_mem]
    intro h
    simp

  -- 対称性: x ∼ y → y ∼ x
  symm := by
    intro x y a
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    exact a.symm
  -- 推移性: x ∼ y ∧ y ∼ z → x ∼ z

  trans := by
    intro x y z a b
    dsimp [vertex_equiv] at a b
    dsimp [vertex_equiv]
    constructor
    · exact (vertexorder_is_preorder SF).le_trans _ _ _ a.1 b.1
    · exact (vertexorder_is_preorder SF).le_trans _ _ _ b.2 a.2
}

lemma vertex_equiv_degree (SF:ClosureSystem α)[DecidablePred SF.sets]:
  ∀ (x y:SF.ground), (vertex_equiv SF) x y →  SF.degree x.val = SF.degree y.val :=
by
  intro x y h
  obtain ⟨hx, hxy⟩ := h.1
  obtain ⟨hy, hyx⟩ := h.2
  have hxy' := hxy SF.ground SF.has_ground
  have hyx' := hyx SF.ground SF.has_ground
  simp_all only [hx, hy, Finset.coe_mem]
  dsimp [SetFamily.degree]
  simp_all only [imp_self, Nat.cast_inj]
  obtain ⟨val, property⟩ := x
  obtain ⟨val_1, property_1⟩ := y
  simp_all only
  congr
  ext x : 2
  simp_all only [and_congr_right_iff]
  intro a
  apply Iff.intro
  · intro a_1
    simp_all only
  · intro a_1
    simp_all only
