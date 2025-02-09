import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Defs
import rooted.RootedCircuits
import rooted.RootedSets
import rooted.Bridge
import LeanCopilot

variable {α : Type} [Fintype α] [DecidableEq α]

--根付き集合のimplicationの関係。pとqからrが推論される。
lemma closuresystem_rootedsets_implication (SF:ClosureSystem α)[DecidablePred SF.sets]:-- [∀ s, Decidable (SF.sets s)]:
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
          --apply Finset.mem_product.mpr
          --simp
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
        simp_all only [implies_true, and_self, true_and, Finset.mem_singleton, Finset.mem_powerset,
          Finset.singleton_subset_iff]
        --simp
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

--ほぼ、定義そのままだが、使うので示しておく。
lemma vertex_equiv_hyperedge (SF:ClosureSystem α)[DecidablePred SF.sets]:
  ∀ (x y:SF.ground), (vertex_equiv SF) x y → ∀ (s:Finset α), SF.sets s →  (x.val ∈ s ↔ y.val ∈ s) :=
by
  intro x y h
  intro s hs
  obtain ⟨hx, hxy⟩ := h.1
  obtain ⟨hy, hyx⟩ := h.2
  have hxy' := hxy s hs
  have hyx' := hyx s hs
  simp_all only [hx, hy, Finset.coe_mem]
  apply Iff.intro
  · intro a
    simp_all only
  · intro a
    simp_all only

--lemma rootedset_setfamily2 (RS : RootedSets α) (SF:ClosureSystem α)
-- (eq:  rootedsetToClosureSystem RS = SF) :
--  ∀ (s : Finset α), s ⊆ SF.ground → (SF.sets s ↔ ¬∃ (p : ValidPair α), p ∈ RS.rootedsets ∧ p.stem ⊆ s ∧ p.root  ∈ (closureOperator SF (s.subtype (λ x => x ∈ SF.ground))).image Subtype.val ∧ p.root ∉ s) :=
--をsingletonに絞って考えたもの。
lemma singleton_hyperedge_lemma (SF:ClosureSystem α) [DecidablePred SF.sets]:
  ∀ (x:SF.ground), SF.sets ({x.val}:Finset α) ↔
  ¬∃ r : ValidPair α, (r ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets ∧ r.stem.card = 1 ∧
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
      simp_all only [Finset.singleton_subset_iff, Finset.coe_mem, subset_refl, Finset.mem_singleton, forall_const, s,
        RS]
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
      simp_all only [Finset.singleton_subset_iff, Finset.coe_mem, subset_refl, Finset.mem_singleton, RS, s]
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
    let hrp :=hr p hp --hrの前提として、ステムが{x}に含まれるpを採用。
    --px : p.stem ⊆ {↑x}より、p.stem = emptyかp.stem = {x.val}で場合分け。
    by_cases p.stem = ∅
    case pos =>
      have :p.stem.card = 0:=
      by
        rename_i s_1 h
        simp_all only [Finset.subset_singleton_iff, true_or, Finset.mem_image, Subtype.exists, exists_and_right,
          exists_eq_right, Finset.card_empty, RS, s_1, s]
      sorry --またおかしいかもしれない。
    case neg =>
      sorry


    --完全表現の根付き集合は、根を固定するとフィルターになっている補題を作った方ががよい。
    --証明の方向が間違っているか確認する。
    --xは、stemだったのにp.root=xを証明するのは少々奇妙だが、あっているのかも。
    --使うのは、hrとprとhxみたい。hrpも使えるかも。pxとhrpからp.stemがemptyであることがいえるかも。

    have : p.stem = ∅ :=
    by
      rename_i s_1
      simp_all only [Finset.subset_singleton_iff, or_false, Finset.mem_image, Subtype.exists, exists_and_right,
        exists_eq_right, s_1, RS, s]
    search_proof
    --p.stemが空集合から矛盾をいいたい。
    --ということは、p.rootはbridgeなので結論がいえると思ったが、この方針は、間違っているかも。{x}がhyperedgeは仮定ではなく結論なので。
    -- prを使って示すのが正しそう。
    simp at pr
    obtain ⟨h_1,pr⟩ := pr
    --extensiveも違う気がする。
    --let efs := extensive_from_SF_finset SF {x}
    --そもそもpを適当に取ったのに、pのrootが{x}に入っているというのがおかしい気がする。
    --RSの定義をひたすら展開すると、矛盾が出るのかも。
    dsimp [rootedSetsFromSetFamily] at hp
    dsimp [rootedSetsSF] at hp
    dsimp [allCompatiblePairs] at hp
    dsimp [isCompatible] at hp
    simp at hp
    obtain ⟨pstem,proot,hp3⟩ := hp
    obtain ⟨hp31,hp32⟩ := hp3
    have hproot:proot = p.root :=
    by
      rename_i s_1
      subst hp32 this
      simp_all only [Finset.subset_singleton_iff, or_false, hrp, s_1, RS, s]
    have hpstem: pstem = p.stem :=
    by
      rename_i s_1
      subst hp32 this
      simp
    let hp31x := hp31.2.2 s
    simp at hp31x
    dsimp [s] at hp31x
    rw [←hproot]
    apply hp31x
    --これも方針が違うような気がしてきた。

    /-  間違った方針かも。
    have :p.root ∈ SF.ground:=
    by
      simp_all only [Finset.subset_singleton_iff, true_or, Finset.mem_image, Subtype.exists, exists_and_right,
        exists_eq_right, RS, s]
      obtain ⟨w, h⟩ := pr
      simp_all only [RS]
    let rsb := (rooted_sets_bridge SF ⟨p.root,this⟩).mpr
    -/
