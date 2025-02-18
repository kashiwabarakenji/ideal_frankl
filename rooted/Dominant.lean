--頂点のdominantの関係について
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
--xとyは異なるとして、parallelを定義したほうがよい？ Definitionのファイルか、Parallel.leanに移す。
--SetFamilyに対して、Parallelを定義した方が良いかも。isParallelという名前のほうがいいかも。Parallel.leanに作る。
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
          --dsimp [Finset.product]
          simp
          constructor
          · simp_all only [Finset.mem_singleton]
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
        --dsimp [Finset.product]
        simp
        constructor
        · --apply Finset.mem_product.mpr
          --simp
          constructor
          · simp_all only [Finset.mem_singleton]
          · simp_all only [Finset.mem_singleton]
        · dsimp [isCompatible]
          simp_all only [Finset.mem_singleton, not_false_eq_true, Finset.singleton_subset_iff, implies_true, and_self]
      · simp_all only [not_false_eq_true, true_and, ne_eq, Finset.card_singleton, and_self]
        simp_all only [Finset.card_singleton, and_self, vpy, vpx, RS]

--vertex orderは、閉集合族Sが最初に与えられた時の、それと両立する順序。
--vertexorderは、preorder.leanのR_hatと似ている。あちらは、RSから導入しているが、こちらは閉集合族から。統一した方がよいかもしれないが、とりあえず、あとまわし。
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
        --dsimp [Finset.product]
        simp
        --apply Finset.mem_product.mpr
        constructor
        simp_all only [implies_true, and_self, true_and, Finset.mem_singleton]
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
--前順序として利用する際には、vertexorderではなくて、こちらの名称を使う必要がある。
--次数が高い方がyである。y dominates xとなる。
instance dominated (SF : ClosureSystem α) [DecidablePred SF.sets] :
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

lemma vertex_dominant_degree (SF:ClosureSystem α)[DecidablePred SF.sets]:
  ∀ (x y:SF.ground), (dominated SF).le x y →  SF.degree x.val ≤ SF.degree y.val :=
by
  intro x y h
  obtain ⟨hx, hxy⟩ := h
  have hxy' := hxy SF.ground SF.has_ground
  simp_all only [hx, Finset.coe_mem]
  dsimp [SetFamily.degree]
  simp_all only [imp_self, Nat.cast_inj]
  simp_all only [Nat.cast_le, ge_iff_le]
  gcongr
  tauto

--dominatedと、closureoperatorの関係。
lemma vertex_dominant_closure (SF:ClosureSystem α)[DecidablePred SF.sets]:
  ∀ (x y:SF.ground), (dominated SF).le x y ↔ y ∈ closureOperator SF {x} :=
by
  intro x y
  apply Iff.intro
  · intro h
    obtain ⟨hx, hxy⟩ := h
    have hxy' := hxy SF.ground SF.has_ground
    simp_all only [hx, Finset.coe_mem]
    rw [mem_closure_iff_lemma]
    intro s hs hxs
    have : x.val ∈ (s.image Subtype.val) :=
    by
      simp_all only [imp_self, Finset.singleton_subset_iff, Finset.mem_image, Subtype.exists, exists_and_right,
        exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]
    convert hxy (s.image Subtype.val) hxs this
    simp

  · intro h
    apply And.intro
    · dsimp [closureOperator] at h
      simp_all only [Finset.map_singleton, Function.Embedding.coeFn_mk, Finset.singleton_subset_iff,
      Finset.mem_subtype, Finset.coe_mem]
    · rw [mem_closure_iff_lemma] at h
      intro s hs hxs
      simp_all only [Finset.singleton_subset_iff]
      let s_sub:= s.subtype (fun x => x ∈ SF.ground)
      have s_eq:Finset.image Subtype.val s_sub = s :=
      by
        ext x
        apply Iff.intro
        · intro a
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
            Finset.coe_mem, Finset.mem_subtype]
          simp_all only [Finset.mem_subtype, exists_prop, s_sub]
        ·
          rename_i x_1
          intro a
          simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
            exists_eq_right_right, true_and, s_sub]
          exact SF.inc_ground s hs a
      rw [←s_eq] at hs
      have :x ∈ s_sub :=
      by
        simp_all only [Finset.mem_subtype, s_sub]
      let hss := h s_sub this hs
      dsimp [s_sub] at hss
      rw [←s_eq]
      simp_all only [s_sub]
      rwa [Finset.mem_subtype] at hss

--closure_singleton_lemma をシングルトンの場合に当てはめたもの。
lemma vertex_dominant_closure2 (SF:ClosureSystem α)[DecidablePred SF.sets]:
  ∀ (x y:SF.ground), (dominated SF).le x y ↔ closureOperator SF {y} ⊆ closureOperator SF {x} :=
by
  intro x y
  apply Iff.intro
  · intro h
    --rw [vertex_dominant_closure] at h
    intro z hz
    rw [←vertex_dominant_closure]
    rw [←vertex_dominant_closure] at hz
    exact le_trans h hz
  · intro h
    let csl := (closure_singleton_lemma SF {x} y).mpr h
    exact (vertex_dominant_closure SF x y).mpr csl



--singleton hyperedgeであることと、ステムサイズが1の根つき集合が存在しないことが同値であるという命題。
--rootedset_setfamily2 やstem_is_upward_closedを使って証明
lemma singleton_hyperedge_lemma (SF:ClosureSystem α) [DecidablePred SF.sets]:
  ∀ (x:SF.ground), SF.sets ({x.val}:Finset α) ↔
  ¬∃ r : ValidPair α, (r ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets ∧ r.root ≠ x.val ∧
  r.stem = ({x.val}:Finset α)) := --このままだと左から右の言明に反例あり。r.stem = empty,r.root ={x.val}
by
  intro x
  let RS := rootedSetsFromSetFamily SF.toSetFamily
  have eq: rootedsetToClosureSystem RS = SF :=
  by
    exact closuresystem_rootedsets_eq SF
  let s:= ({x.val}:Finset α)
  have incsg: s ⊆ SF.ground :=
    by
      simp_all only [Finset.singleton_subset_iff, Finset.coe_mem, RS, s]

  apply Iff.intro
  · intro ssx
    by_contra h_contra
    obtain ⟨r, hr1,hr2 ⟩ := h_contra

    let rss:= (rootedset_setfamily2 RS SF eq s incsg).mp
    have: SF.sets s :=
    by
      dsimp [s]
      simp_all [s, RS]
    specialize rss this
    rw  [not_exists] at rss
    specialize rss r
    simp at rss
    dsimp [RS] at rss
    specialize rss hr1
    dsimp [s] at rss
    have :r.stem ⊆ {x.val} :=
    by
      simp_all only [Finset.singleton_subset_iff, Finset.coe_mem, Finset.mem_singleton]
    specialize rss this
    have : r.root ∈ SF.ground :=
    by
      exact (RS.inc_ground r hr1).2
    specialize rss this
    have : r.root ∈ ({x.val}:Finset α) :=
    by
      apply rss
      --⟨r.root, ⋯⟩ ∈ closureOperator SF (Finset.subtype (fun x => x ∈ SF.ground) {↑x})
      --ステムのclosureをとるとrootを含むという補題を使う必要がある。
      let rsc := root_stem_closure SF r hr1
      simp at rsc
      dsimp [rootedpair_to_subtype] at rsc
      convert rsc
      simp_all only [Finset.singleton_subset_iff, Finset.coe_mem, subset_refl]
    let rr := r.root_not_in_stem
    simp [hr2] at rr
    simp_all only [Finset.singleton_subset_iff, Finset.coe_mem, subset_refl, implies_true,Finset.mem_singleton, s, RS]
  · --push_neg
    intro hr --証明の方針としては、hrは、rootedset_setfamily2が成り立つ前提の特殊ケースなのでhrから前提が成り立つよねってことを示す。
    let s:= ({x.val}:Finset α)
    let rss:= (rootedset_setfamily2 RS SF eq s incsg).mpr
    dsimp [RS] at rss
    dsimp [s] at rss
    apply rss
    push_neg
    intro p hp
    intro px
    intro pr
    push_neg at hr
    by_contra h_contra
    simp at h_contra
    let hrp :=hr p hp h_contra --hrの前提として、ステムが{x}に含まれるpを採用。
    have emp: p.stem = ∅ :=
    by
      rename_i s_1
      simp_all only [Finset.subset_singleton_iff, or_false, Finset.mem_image, Subtype.exists, exists_and_right,
        exists_eq_right, s_1, RS, s]
    have :p.root ∉ s :=
    by
      rename_i s_1
      simp_all only [Finset.subset_singleton_iff, true_or, Finset.mem_image, Subtype.exists, exists_and_right,
        exists_eq_right, Finset.mem_singleton, not_false_eq_true, RS, s_1, s]

    let p' := ValidPair.mk s p.root this
    let siu := stem_is_upward_closed SF p p' hp
    have pp: p.root = p'.root :=
    by
      simp_all only [Finset.subset_singleton_iff, true_or, Finset.mem_image, Subtype.exists, exists_and_right,
        exists_eq_right, RS, s, p']
    specialize siu pp
    have : p.stem ⊆ p'.stem :=
    by
      rw [emp]
      simp
    specialize siu this
    have : p'.stem ⊆ SF.ground :=
    by
      dsimp [p']
      exact incsg
    specialize siu this
    let hrp :=hr p' siu
    have :p'.root ≠ x.val:=
    by
      rw [pp]
      exact h_contra
    specialize hrp this
    contradiction
