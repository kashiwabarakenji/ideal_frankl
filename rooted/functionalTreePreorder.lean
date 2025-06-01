--前順序に関するpathの議論。PreorderPathとかの名前にしてもよかった。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Tactic
import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne
import rooted.functionalCommon

open Finset Set Classical

set_option maxHeartbeats 500000

variable {α : Type} [Fintype α] [DecidableEq α]

--前半は、Setupに関係する補題を示す。Commonの続き的な内容。
--fの連鎖で届くことと、preorderの大小が同値であることを示す。
--後半は、考えている前順序集合に関する補題。
--このファイルのメイン定理は、function fから作られるpreorderから引き起こされるsetoidの同値類において、同値類の大きさが2以上であれば、極大要素になっているという定理eqClass_size_ge_two_implies_inverse

--Commonのle_eq_Rの内容とかぶっている。
private lemma size_one_preorder_setup_lemma (s: Setup α) (x y : {x : α // x ∈ s.V}) :
  s.pre.le x y ↔  @Relation.ReflTransGen s.V (R_from_RS1 (rootedset_from_setup s))  y x:=
by
  simp [rootedset_from_setup]
  rw [s.h_pre]
  dsimp [size_one_preorder]
  dsimp [size_one_circuits_preorder]
  dsimp [rootedset_onestem_eachvertex_V]
  apply Iff.intro
  · intro h
    apply preorder.R_hat.to_ReflTransGen
    exact h

  · intro h
    intro s1 hs1
    exact preorder.ReflTransGen.to_R_hat h s1 hs1

--fで直前関係になっていれば、a <= bとなること。自明かと思っていたけど、深く定義を追っていかないと証明できなかった。
--path_implies_leもsize_one_preorder_setup_step も、ファイル外のfq_lemma_rev_oneこの補題を参照。
--これはcommonに移動させてもいいかも。
theorem f_and_pre (su: Setup α) (a b : {x // x ∈ su.V}) (sf : su.f a = b ) : su.pre.le a b := by
  rw [su.h_pre]
  dsimp [size_one_preorder]
  dsimp [size_one_circuits_preorder]
  dsimp [preorder.R_hat]
  intro s hs hhs
  dsimp [preorder.S_R] at hs
  rw [Finset.mem_filter] at hs
  dsimp [rootedset_onestem_eachvertex_V] at hs
  simp at hs
  dsimp [preorder.closedUnder] at hs
  let hs2 := hs.2
  dsimp [R_from_RS1] at hs2
  simp at hs2
  specialize hs2 b b.property
  specialize hs2 a a.property
  have : a.val ∉ ({b.val}:Finset α) := by
    intro h
    rw [Finset.mem_singleton] at h
    rw [←sf] at h
    let suv := su.valid a
    have : a = (su.f a) := by
      exact Subtype.eq h
    rw [←this] at suv
    contradiction
  let vp := ValidPair.mk {b.val} a.val this
  specialize hs2 vp
  simp at hs2
  specialize hs2 a
  simp at hs2
  apply hs2
  dsimp [vp]
  ext
  · simp
    rw [sf]
  · simp
  · dsimp [vp]
  · dsimp [vp]
  · exact hhs

-------ここからfの繰り返しに関する部分------

--iterationは、functionalSPOでは、setup_spo前提だがreachと書かれていて、一部は利用されていて、一部は重複ている可能性がある。
--iterationで辿り着くものには、大小関係がある。

--証明には f_and_preが利用している。
--外からは参照されてないかも。iteratef_lemma_twoから参照されている。

private lemma iteratef_lemma (s: Setup α) (x : s.V):
  ∀ n, s.pre.le x (s.f^[n] x) := by
  intro n
  induction n generalizing x
  case zero =>
      simp_all only [Function.iterate_zero, id_eq, le_refl]

  case succ n ih =>
      rw [Function.iterate_succ]
      simp
      have ihh:s.pre.le (s.f x) (s.f^[n] (s.f x)) := by
        simp_all only [Subtype.forall]
      have : s.pre.le (x) (s.f x) := by
        apply f_and_pre
        simp_all only [Subtype.forall]
      exact s.pre.le_trans x (s.f x) (s.f^[n] (s.f x)) this ihh

--pathを使わずにiteratef_lemma_refを証明する。
private lemma exists_iterate_eq_of_rtg
    {α : Type} [Fintype α] [DecidableEq α]
    {s : Setup α} {x y : s.V}
    (h : Relation.ReflTransGen (fun a b : s.V ↦ s.f a = b) x y) :
  ∃ n : ℕ, (s.f^[n]) x = y := by
  induction h with
  | refl      => exact ⟨0, rfl⟩
  | tail h₁ h₂ ih =>
      rcases ih with ⟨n, rfl⟩           -- 途中点 = f^[n] x
      exact ⟨n.succ, by
        rename_i c
        rw [←h₂]
        rw [Function.iterate_succ' s.f n]
        exact rfl
      ⟩

--transitive closureを撮る前の一歩の場合の表現の違いに関する補題。Setup前提の形にした。
--そとファイルからの参照はない。
private lemma size_one_preorder_setup_step (s: Setup α) (x y : {x : α // x ∈ s.V}) :
  R_from_RS1 (rootedset_from_setup s) y x ↔ s.f x = y :=
by
  dsimp [rootedset_from_setup]
  dsimp [rootedset_onestem_eachvertex_V]
  dsimp [R_from_RS1]
  apply Iff.intro
  · intro h
    simp [rootedset_onestem_eachvertex_V] at h
    obtain ⟨val, property⟩ := h
    obtain ⟨val_1, property_1⟩ := property
    obtain ⟨val_2, property_2⟩ := property_1
    obtain ⟨val_2, property⟩ := x
    obtain ⟨val_3, property_1⟩ := y
    obtain ⟨w, h⟩ := val_1
    obtain ⟨w_1, h⟩ := h
    subst h val_2
    simp_all only [singleton_inj]
    subst property_2
    simp_all only [Subtype.coe_eta]
  · intro h
    have : x.val ∉ ({y.val} :Finset α):=
    by
      rw [←h]
      simp
      by_contra h_contra
      have noteq:  ¬ ↑x = ↑(s.f x) :=
      by
        let sv := s.valid x
        exact id (Ne.symm sv)
      have :(s.f x) = x := by
        apply Subtype.eq
        subst h
        simp_all only
      rw [this] at noteq
      contradiction

    let vp := ValidPair.mk {y.val} x.val this
    use vp
    simp
    constructor
    ·
      subst h
      simp_all only [ValidPair.mk.injEq, singleton_inj, exists_and_right, exists_eq_right, Subtype.coe_eta, coe_mem,
        exists_const, vp]
    ·
      subst h
      simp_all only [and_self, vp]

---そとから使われてない。より使いやすい他のを引用した方が良いので。
-- fから順序を定義するのに、この方法のほうがシンプルかもしれないが。
--size_one_preorder_setup_lemma2から名称変更
private lemma  size_one_preorder_eq_transition (s : Setup α) (x y : s.V):
  s.pre.le x y ↔
  Relation.ReflTransGen (fun a b : s.V ↦ s.f a = b) x y := by
  let sop := size_one_preorder_setup_lemma s x y
  --let sop3 := Iff.symm (size_one_preorder_setup_step s x y)
  have : (R_from_RS1 (rootedset_from_setup s)) = (fun b a : s.V ↦ s.f a = b):= by
    --obtain ⟨val, property⟩ := x
    --obtain ⟨val_1, property_1⟩ := y
    ext a b
    let sop3 := Iff.symm (size_one_preorder_setup_step s a b)
    exact size_one_preorder_setup_step s b a

  have :Relation.ReflTransGen (R_from_RS1 (rootedset_from_setup s)) y x ↔
    Relation.ReflTransGen (fun a b : s.V ↦ s.f a = b) x y := by
    rw [this]
    exact Relation.reflTransGen_swap

  exact Iff.trans sop this

--これが証明したかった定理。preorderで大小関係があれば、reachで届く。
--外から参照されている。
theorem iteratef_lemma_ref
    (s : Setup α) (x y : s.V)
    (h : s.pre.le x y) :
  ∃ n : ℕ, (s.f^[n]) x = y := by
  -- `le` → 反射推移閉包
  have h' : Relation.ReflTransGen (fun a b : s.V ↦ s.f a = b) x y :=
    (size_one_preorder_eq_transition s x y).1 h
  -- 反射推移閉包 → 反復回数
  exact exists_iterate_eq_of_rtg h'


--iterationの回数と大小関係。
--pathの議論は使っていない。
private lemma iteratef_lemma_two (s: Setup α) (x: s.V) (n1 n2: Nat) :
  n1 < n2 → s.pre.le (s.f^[n1] x) (s.f^[n2] x) :=
by
  -- ここで f の n 回の反復を考えます
  intro h
  let n := n2 - n1
  have : n + n1 = n2 := by
    simp_all only [n]
    obtain ⟨val, property⟩ := x
    omega
  have : s.f^[n] (s.f^[n1] x) = s.f^[n2] x := by
    rw [←this]
    rw [Function.iterate_add]
    exact rfl
  let il := iteratef_lemma s (s.f^[n1] x) n
  rw [this] at il
  exact il

--補題:fのiterationの全体は、重複しているものがある。
--証明：鳩の巣原理。 Fintype.exists_ne_map_eq_of_card_ltがポイント。
--pathの議論は使っていない。
private lemma iteratef_pigeon (s: Setup α) (x: s.V)  : ∃ (n1 n2: Nat), n1 ≠ n2 ∧ (s.f^[n1] x) = s.f^[n2] x :=
by
  let dom := (Finset.Icc 0 (s.V.card + 1)).image (fun i => (s.f^[i] x))
  have : s.V.card < ((Finset.Icc 0 (s.V.card + 1))).card := by
    simp_all only [Nat.card_Icc, tsub_zero, ge_iff_le]
    obtain ⟨val, property⟩ := x
    linarith
  have : Fintype.card { x // x ∈ s.V } < Fintype.card (Finset.Icc 0 (s.V.card + 1)) :=
  by
    simp_all only [Nat.card_Icc, tsub_zero, Fintype.card_coe, Finset.mem_Icc, zero_le, true_and]
  have : Fintype.card { x // x ∈ s.V } < Fintype.card (Fin (#s.V + 1)) := by
    simp_all only [Nat.card_Icc, tsub_zero, Fintype.card_coe, Finset.mem_Icc, zero_le, true_and, Fintype.card_fin,
      lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt]

  let fe := @Fintype.exists_ne_map_eq_of_card_lt (Fin (s.V.card + 1)) s.V _ _ (λ i=> s.f^[i.val] x) this
  obtain ⟨n1, n2, h⟩ := fe
  use n1, n2
  simp_all only [Nat.card_Icc, tsub_zero, Fintype.card_coe, Finset.mem_Icc, zero_le, true_and, Fintype.card_fin,
    lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, ne_eq, and_true]
  obtain ⟨val, property⟩ := x
  obtain ⟨left, right⟩ := h
  apply Aesop.BuiltinRules.not_intro
  intro a
  simp_all only
  omega

--上の定理の大小関係を整えたものを出力する定理
private lemma iteratef_pigeon_ordered (s : Setup α) (x : s.V) :
  ∃ (n1 n2 : ℕ), n1 < n2 ∧ (s.f^[n1] x) = (s.f^[n2] x) := by
  obtain ⟨n1, n2, hne, heq⟩ := iteratef_pigeon s x
  by_cases h : n1 < n2
  · exact ⟨n1, n2, h, heq⟩
  · have h' : n2 < n1 := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) hne.symm
    simp_all only [ne_eq, not_lt]
    obtain ⟨val, property⟩ := x
    apply Exists.intro
    · apply Exists.intro
      · apply And.intro
        · exact h'
        · simp_all only

  --補題：何回もiterationすると、サイズが2以上の同値類に辿り着く。
  --証明：鳩の巣の上の補題のn1とn2のノードは同じで、その次のノードは、異なるが同じ同値類に属するノードになる。
private lemma iteratef_size2 (s: Setup α) (x: s.V)  : ∃ (n : Nat), 2 ≤ (eqClass_setup s (s.f^[n] x)).card :=
by
  let h := iteratef_pigeon_ordered s x
  /- hの別の分解の仕方。参考まで。
  cases h with
  | intro n1 h' =>
    cases h' with
    | intro n2 h'' =>
      cases h'' with
      | intro hneq heq =>
      -- ここで n1, n2, hneq, heq が使える
  -/
  --obtain ⟨n1, n2, hneq, heq⟩ : ∃ n1 n2, n1 ≠ n2 ∧ s.f^[n1] x = s.f^[n2] x := h
  obtain ⟨n1, n2, hneq, heq⟩ := h
  let y := s.f^[n1] x
  let z := s.f^[n1+1] x
  have y12: y = s.f^[n2] x := by
    simp_all only [y]
  have fzy: z = s.f y := by
    dsimp [y]
    exact Function.iterate_succ_apply' s.f n1 x
  have neqyz: y ≠ z := by
    intro h
    rw [fzy] at h
    let hnot :=  s.valid y
    rw [Eq.symm h] at hnot
    contradiction
  have : s.pre.le y z := by
    exact f_and_pre s y z (id (Eq.symm fzy))
  have : n2 > n1 + 1:= by
    by_cases n2 = n1 + 1
    case pos h =>
      rw [h] at y12
      rw [h] at hneq
      have : y = s.f (s.f^[n1] x) :=
      by
        exact False.elim (neqyz y12)
      have :y = s.f y := by
        exact this
      have :y ≠ s.f y := by
        exact fun a => neqyz y12
      contradiction
    case neg h =>
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, y, z]
      omega

  have : s.pre.le z y := by
    --zからyにfで行けるので、s.pre.le z yとなる。
    let ilt := iteratef_lemma_two s x (n1+1) n2 this
    dsimp [y,z]
    simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, ge_iff_le, y, z]
    rwa [← fzy]
  have yineq: y ∈ eqClass_setup s y := by
    simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, y, z]
    rw [eqClass_setup]
    simp_all only [mem_filter, mem_attach, true_and]
    rfl

  have : z ∈ eqClass_setup s y := by
    dsimp [eqClass_setup]
    simp_all only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, mem_attach, y, z]
    ·
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, y, z]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      obtain ⟨val_2, property_2⟩ := z
      symm
      rw [← fzy]
      simp_all only
      symm
      rw [← fzy]
      simp_all only
      induction s
      rename_i h_pre h_setoid po this_2
      subst h_pre h_setoid
      simp_all only [AntisymmRel.setoid_r]
      constructor
      · simp_all only
      · simp_all only
  have : (eqClass_setup s y).card ≥ 2 := by
    dsimp [eqClass_setup]
    simp_all only [Finset.card_filter, Finset.card_univ, true_and, Finset.mem_univ, Finset.mem_filter]
    --zも(eqClass_setup s y).cardの要素で、neqyzなので、同値類の大きさは2以上。
    have hsub : {y, z} ⊆ eqClass_setup s y := by
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, y, z]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      obtain ⟨val_2, property_2⟩ := z
      intro x hx
      simp_all only [Finset.mem_insert, Finset.mem_singleton]
      obtain ⟨val_3, property_3⟩ := x
      cases hx with
      | inl h => simp_all only
      | inr h_1 => simp_all only
    have hsub_card: ({y,z}:Finset s.V).card ≤ (eqClass_setup s y).card := by
      exact Finset.card_le_card hsub
    have :({y,z}:Finset s.V).card = 2:= by
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, Finset.mem_singleton,
        not_false_eq_true, card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd, y, z]
    rw [this] at hsub_card
    simp
    simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, Finset.mem_singleton,
      not_false_eq_true, card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd, y, z]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    obtain ⟨val_2, property_2⟩ := z
    exact hsub_card

  use n1

--Setup前提のs.Vの要素の極大の定義。
--これもCommonに移動してもよい。
def isMaximal (s: Setup α) (a : s.V) : Prop :=
  ∀ b : s.V, s.pre.le a b → s.pre.le b a

--任意の要素の上には、maximalな要素が存在するという定理を作ってもよい。

/--
`2 ≤ s.card` ならば
`a , b ∈ s` かつ `a ≠ b` となる 2 点 `a , b` が存在する。
-/
private lemma card_ge_two {α : Type} {s : Finset α}
    (h : (2 : ℕ) ≤ s.card) :
    ∃ a b : α, a ∈ s ∧ b ∈ s ∧ a ≠ b :=
by
  ----------------------------------------------------------------
  -- 1. まず `a ∈ s` を 1 つ取り出す
  ----------------------------------------------------------------
  have h_pos : 0 < s.card := by
    have : (0 : ℕ) < 2 := by decide
    exact Nat.lt_of_lt_of_le this h
  rcases (Finset.card_pos.mp h_pos) with ⟨a, ha⟩

  ----------------------------------------------------------------
  -- 2. `s.erase a` の要素数は少なくとも 1
  ----------------------------------------------------------------
  have h_card_erase : 1 ≤ (s.erase a).card := by
    have h_eq : (s.erase a).card + 1 = s.card :=
      Finset.card_erase_add_one ha
    have : 2 ≤ (s.erase a).card + 1 := by
      simpa [h_eq] using h
    exact Nat.le_of_succ_le_succ this
  have h_pos_erase : 0 < (s.erase a).card :=
    Nat.succ_le_iff.mp h_card_erase

  ----------------------------------------------------------------
  -- 3. `b ∈ s.erase a` を 1 つ取り出す
  ----------------------------------------------------------------
  rcases (Finset.card_pos.mp h_pos_erase) with ⟨b, hb_in_erase⟩
  rcases (Finset.mem_erase).1 hb_in_erase with ⟨hneq_ba, hb⟩

  ----------------------------------------------------------------
  -- 4. 2 点 `a , b` と必要な条件をまとめる
  ----------------------------------------------------------------
  exact ⟨a, b, ha, hb, hneq_ba.symm⟩

-----------------------------------------------------------------------
-- このあたりから、応用-------

--同値類の大きさが2以上のところは極大要素であるを証明するための補題。
private lemma eqClass_size_ge_two_implies_outside
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α) :
    ∀ y : {x // x ∈ s.V},
      2 ≤ (eqClass_setup s y).card →
      s.f y ∈ eqClass_setup s y :=
by
  intro y hcard

  ----------------------------------------------------------------
  -- 1. 同値類から y とは異なる要素 z を 1 つ取り出す
  ----------------------------------------------------------------
  have htwo : (eqClass_setup s y).card ≥ 2 := hcard
  obtain ⟨a, b, ha, hb, hne⟩ := (card_ge_two htwo)   -- 2 個以上あるとき，互いに異なる 2 点が取れる
  -- a または b が y と異なればそれを z とする
  set z : {x // x ∈ s.V} :=
    if h : (a : {x // x ∈ s.V}) ≠ y then a else b with hz_def
  have hz_mem : z ∈ eqClass_setup s y := by
    by_cases h : (a : {x // x ∈ s.V}) ≠ y
    · simp [hz_def, h, ha]
    · have : (b : {x // x ∈ s.V}) ≠ y := by
        intro hby
        have : (a : {x // x ∈ s.V}) = b := by
          have : a = y := Subtype.ext (by
            subst hby
            simp_all only
          )
          have : (a : {x // x ∈ s.V}) = (y : {x // x ∈ s.V}) := this
          simpa [hby] using this
        exact (hne this).elim
      simp [hz_def, h, hb, this]

  have hrel : s.setoid.r y z := by
    -- `eqClass_setup` は `filter` で `setoid.r` を課している
    have := (Finset.mem_filter.mp hz_mem).2
    exact this

  ----------------------------------------------------------------
  -- 2. `y ≤ z` を iteration へ変換し，反復回数 n (≥1) を取る
  ----------------------------------------------------------------
  have hle : s.pre.le y z := by
    -- `setoid_preorder` の定義より
    exact eqClass_le s y z hz_mem
  obtain ⟨n, hn⟩ := iteratef_lemma_ref s y z hle   -- ∃ n, f^[n] y = z
  have hn_pos : 0 < n := by
    by_contra hn0
    have hn00 : n = 0 := by
      exact Nat.eq_zero_of_le_zero (Nat.le_of_not_lt hn0)
    have hzy: z = y := by
      rw [hn00] at hn
      exact id (Eq.symm hn)
    have : z ≠ y := by
      -- z は y と異なる
      by_cases (a : {x // x ∈ s.V}) ≠ y
      · subst hn00
        simp_all only [ge_iff_le, ne_eq, dite_eq_ite, not_false_eq_true, ↓reduceIte, ↓reduceDIte, z]

      ·
        subst hn00
        simp_all only [ge_iff_le, ne_eq, dite_eq_ite, ↓reduceIte, ↓reduceDIte, Decidable.not_not, Function.iterate_zero,
          id_eq, not_true_eq_false, lt_self_iff_false, not_false_eq_true, z]
    exact this hzy

  ----------------------------------------------------------------
  -- 3. 反復の 1 ステップ目 `f y` が同値類に入ることを示す
  ----------------------------------------------------------------
  -- (i) y ≤ fy
  have hle_y_fy : s.pre.le y (s.f y) := by
    simpa using f_and_pre s y (s.f y) rfl

  -- (ii) fy ≤ z
  have hle_fy_z : s.pre.le (s.f y) z := by
    -- n = (n-1)+1 なので iteratef_lemma をもう一度
    have : s.pre.le (s.f y) (s.f^[n - 1] (s.f y)) :=
      iteratef_lemma s (s.f y) (n - 1)

    rw [←@Function.comp_apply _ _ _ (s.f^[n - 1]) s.f ] at this
    rw [←@Function.iterate_succ _ s.f (n-1)] at this
    simp [Nat.sub_add_cancel hn_pos]
    have nsucc: (n-1).succ = n := by
      simp [Nat.sub_add_cancel hn_pos]
    rw [nsucc] at this
    exact le_of_le_of_eq this hn

  -- (iii) z ≤ y  も hrel から取れる
  have hle_z_y : s.pre.le z y := by
    exact eqClass_ge s y z hz_mem

  -- (iv) 以上より y ≤ fy ∧ fy ≤ y
  have hfy_y : s.pre.le (s.f y) y :=
    s.pre.le_trans (s.f y) z y hle_fy_z hle_z_y
  have hy_fy : s.pre.le y (s.f y) := hle_y_fy

  ----------------------------------------------------------------
  -- 4. 前後で ≤ が成り立つ ⇒ setoid.r
  ----------------------------------------------------------------
  have hrel_fy : s.setoid.r y (s.f y) := by
    -- `setoid_preorder` は左右の ≤ が揃えば成り立つ
    suffices (s.pre.le y (s.f y)) ∧ (s.pre.le (s.f y) y) from by
      rw [s.h_setoid]
      exact this

    simp [hy_fy, hfy_y]

  ----------------------------------------------------------------
  -- 5. filter の条件を満たすので `f y` は同値類に属する
  ----------------------------------------------------------------
  show s.f y ∈ eqClass_setup s y

    -- `attach` に必ず入っているので条件は r のみ
  have hmem : (s.f y) ∈ s.V.attach := by
    -- `s.f y` は V の要素
    simp [Finset.mem_attach]    -- automatically true by `.attach`
  have : s.setoid.r y (s.f y) := hrel_fy
  exact Finset.mem_filter.mpr ⟨hmem, this⟩

private lemma cycle_exists
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α) (x : {x // x ∈ s.V})
    (h₂ : 2 ≤ (eqClass_setup s x).card) :
    ∃ p : ℕ, 0 < p ∧ s.f^[p] x = x := by
  -- `f x` は同値類にとどまる → `f x ≤ x`
  have h_fx_in : s.f x ∈ eqClass_setup s x :=
    eqClass_size_ge_two_implies_outside s x h₂
  have h_fx_le_x : s.pre.le (s.f x) x :=
    eqClass_ge s x (s.f x) h_fx_in
  -- `f x ≤ x` から「いつか戻って来る」回数 `m`
  rcases iteratef_lemma_ref s (s.f x) x h_fx_le_x with ⟨m, hm⟩
  -- 周期 `p = m.succ (>0)` で `x` に戻る
  refine ⟨m.succ, Nat.succ_pos _, ?_⟩
  -- f^[m+1] x = f^[m] (f x) = x
  exact hm

/--
`f^[p] x = x` なら任意の `k` について `f^[p*k] x = x`
-/
private lemma iterate_power_cycle
    {α : Type} (f : α → α) (x : α) {p : ℕ}
    (_ : 0 < p) (hcycle : f^[p] x = x) : --p正の仮定は使ってないように見えて使っている？
    ∀ k : ℕ, f^[p * k] x = x := by
  intro k
  induction k with
  | zero     => exact rfl
  | succ k ih =>
      -- f^[p*(k+1)] = f^[p] (f^[p*k])
      have hpk: p * (k + 1) = p + p * k := by ring
      have :f^[p*(k+1)] x = f^[p] ((f^[p*k]) x):= by
        rw [←@Function.comp_apply _  _ _ (f^[p]) f^[p*k] x]
        rw [←Function.iterate_add]
        exact congrFun (congrArg (Nat.iterate f) hpk) x

        -- `f^[p] x = x` なので `f^[p*(k+1)] x = x`

      rw [this]
      simp_all only


--サイズ 2 以上の同値類に属する点は極大
-- SPO2で使っている。そこでの仮定は、Setup2
theorem eqClass_size_ge_two_implies_inverse
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α) (x : {x // x ∈ s.V})
    (h₂ : 2 ≤ (eqClass_setup s x).card) :
    isMaximal s x := by
  -- 周期 `p`
  obtain ⟨p, hp_pos, hcycle⟩ := cycle_exists s x h₂
  -- 反復 `p*k` は常に `x`
  have hpow := iterate_power_cycle s.f x hp_pos hcycle
  -- 極大性の証明
  intro y h_xy            -- 仮定 `x ≤ y`
  -- `y = f^[n] x` を取得
  rcases iteratef_lemma_ref s x y h_xy with ⟨n, rfl⟩
  -- n = 0 なら y = x で終わり
  cases n with
  | zero    => simp
  | succ n₀ =>
      -- 剰余 `r = (n₀.succ) % p`
      let r := (n₀.succ) % p
      have hr_lt : r < p := Nat.mod_lt _ hp_pos
      by_cases hr0 : r = 0
      ----------------------------------------------------------------
      -- ① 剰余が 0 なら y = x（x ≤ x は自明）
      ----------------------------------------------------------------
      ·
        have : s.f^[n₀.succ] x = x := by
          -- n₀.succ = q*p なので周期で戻る
          have h1 : n₀.succ = p * (n₀.succ / p) := by
            simp_all only [Function.iterate_succ, Function.comp_apply, Nat.succ_eq_add_one, r]
            obtain ⟨val, property⟩ := x
            rw [Nat.mul_div_cancel']
            omega
            --simpa [Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mod_eq_zero hr0)]
            --      using (Nat.mod_add_div _ p).symm
          -- 置換

          rw [h1]
          exact hpow (n₀.succ / p)

        simp [hr0, this]
      ----------------------------------------------------------------
      -- ② 剰余が正なら `m = p - r` で y →* x
      ----------------------------------------------------------------
      ·
        have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
        let m : ℕ := p - r        -- 0 < m ≤ p
        have hm_pos : 0 < m := Nat.sub_pos_of_lt hr_lt
        -- `y ≤ f^[m] y`
        have h_y_step : s.pre.le (s.f^[n₀.succ] x)
                                   (s.f^[m] (s.f^[n₀.succ] x)) :=
          iteratef_lemma s (s.f^[n₀.succ] x) m
        -- 計算 `f^[m] y = x`
        have h_to_x : s.f^[m] (s.f^[n₀.succ] x) = x := by
          -- n₀.succ = q*p + r なので n₀.succ + m = (q+1)*p
          have hdecomp : n₀.succ = p * (n₀.succ / p) + r :=
          by
            simp_all only [Function.iterate_succ, Function.comp_apply, Nat.succ_eq_add_one, tsub_pos_iff_lt, r, m]
            obtain ⟨val, property⟩ := x
            rw [Nat.div_add_mod]
          have hsum : n₀.succ + m = p * ((n₀.succ / p) + 1) := by
            have : m = p - r := rfl; simp [m, hdecomp, Nat.add_sub_cancel] at *
            rw [hdecomp]
            calc
              p * ((n₀ + 1) / p) + r + (p - r) = p * ((n₀ + 1) / p) + p :=
              by
                have : r + (p - r) = p := by
                  simp_all only [Nat.add_sub_cancel]
                  refine Nat.add_sub_of_le ?_
                  exact Nat.le_of_succ_le hm_pos
                exact Mathlib.Tactic.Ring.add_pf_add_lt (p * ((n₀ + 1) / p)) this

              _ = p * ((n₀ + 1) / p + 1) :=
              by
                rw [mul_add_one]
              _= p * ((p * ((n₀ + 1) / p) + r) / p + 1) :=
              by
                symm
                exact
                  (Nat.mul_left_cancel_iff hp_pos).mpr
                    (congrFun
                      (congrArg HAdd.hAdd (congrFun (congrArg HDiv.hDiv (id (Eq.symm hdecomp))) p))
                      1)

          have sfsf: s.f^[n₀.succ + m] x =
                  s.f^[p * ((n₀.succ / p) + 1)] x := by
            exact congrFun (congrArg (Nat.iterate s.f) hsum) x
          have := congrArg (fun t => t)
                  (by
                    -- 反復の足し算
                    exact hcycle
                  )

          -- 右辺を周期で縮約
          simp [this, hpow]
          rename_i h1
          rw [←@Function.comp_apply _ _ _ s.f^[n₀] s.f]
          rw [←Function.iterate_succ]
          rw [←@Function.comp_apply _ _ _ s.f^[m] s.f^[n₀.succ]]
          rw [←Function.iterate_add]
          rw [add_comm]
          rw [hsum]
          exact hpow (n₀.succ / p + 1)

        -- まとめ： y ≤ x
        simp [h_to_x]
        exact le_of_le_of_eq h_y_step h_to_x


-------------------------------------------------------------
--同じ同値類のfの行き先は、同値になることを示す必要がある。あとで外からも使っている。
--TreePartialから利用している。
--eqClass_size_ge_two_implies_outsideに依存している。
theorem f_on_equiv
  (s: Setup α) (x y: s.V) (h: s.setoid.r x y) :
  s.setoid.r (s.f x) (s.f y) :=
by
  have eqy: eqClass_setup s x = eqClass_setup s y := by
      apply eqClass_eq
      · rw [s.h_setoid] at h
        rw [setoid_preorder] at h
        simp [equiv_rel] at h
        simp_all only
      · rw [s.h_setoid] at h
        rw [setoid_preorder] at h
        simp [equiv_rel] at h
        simp_all only
  have xineq: x∈ eqClass_setup s x := by
          simp_all only [eqClass_setup]
          simp
          rw [s.h_setoid]
          rw [setoid_preorder]
          simp [equiv_rel]
          rw [s.h_setoid] at h
          rw [setoid_preorder] at h
          simp [equiv_rel] at h
          simp_all only [ge_iff_le, not_le, and_self]

  have yineq: y ∈ eqClass_setup s x := by
      simp_all only [eqClass_setup]
      rw [s.h_setoid] at h
      rw [setoid_preorder] at h
      simp [equiv_rel] at h
      simp_all only [mem_filter, mem_attach, true_and]
      rfl

  by_cases h1: (eqClass_setup s x).card ≥ 2;
  case pos =>
    let eqsx := eqClass_size_ge_two_implies_outside s x h1
    have : s.f x ∈ eqClass_setup s x := by
      simp_all only [eqsx]
      rwa [← eqy]
    have : s.f y ∈ eqClass_setup s y := by
      have :(eqClass_setup s y).card ≥ 2 := by
        rw [←eqy]
        exact h1
      exact eqClass_size_ge_two_implies_outside s y this
    rw [←eqy] at this
    rw [s.h_setoid]
    rw [setoid_preorder]
    simp
    dsimp [equiv_rel]
    let eqe := (eqClass_eq_rev s (s.f x) (s.f y) x)
    specialize eqe eqsx
    specialize eqe this
    constructor
    · exact eqe.1
    · exact eqe.2
  case neg =>
    --同値類の大きさが1のとき。
    --同値類の大きさが1であれば、同値のものは一致する。
    have :(eqClass_setup s x).card = 1 := by
      --cardは1以上で2以上でないので、ちょうど1になる。
      have geq1:(eqClass_setup s x).card ≥ 1 := by

        have :(eqClass_setup s x).Nonempty := by
          simp_all only [ge_iff_le, not_le]
          exact ⟨_, xineq⟩
        exact Finset.card_pos.mpr this
      have leq1: (eqClass_setup s x).card  ≤ 1 := by
        simp_all only [ge_iff_le, not_le, one_le_card]
        omega
      exact Eq.symm (Nat.le_antisymm geq1 leq1)

    have :x = y := by
      obtain ⟨xx,hxx⟩ := Finset.card_eq_one.mp this
      rw [hxx] at yineq
      rw [hxx] at xineq
      simp at xineq
      simp at yineq
      rw [←yineq] at xineq
      exact xineq
    subst this
    rfl


/-
--逆向き。今のところ使わなくても、示したいことは示せているかも。
lemma f_on_equiv_rev
  (s: Setup2 α) (x y: s.V) (h: s.setoid.r (s.f x) (s.f y)) :
  s.setoid.r x y :=
by
-/

/-
----ここから下はPathに依存している議論。落ち着いたら消してもよい。
--Preorderのstar_implies_pathExistsでも同じことを証明している。大きい方から小さい方の鎖になっているような。
--このあたりはSetup前提ではないが、Setup前提のpath_exists_setup_reverse の証明で使っている。
--最終的には、path_exists_setupに生かされる。
--でも、fのiterationでないパスのアプローチは、初期のアプローチなので、全体からは浮いているかも。Setupも使ってないし。
--パスが存在することと、fのiterationで到達できることが同値であるという命題は、iteratef_lemma_ref。
--本質的には、矢印を辿ることになるので、pathの手法とは変わらないかもしれないが、最初からSetupを使っていればもっと短くかけた。
--でも、短く書き直すことが重要でないような気もするので、そのままでもいいかも。

--この補題の参照は、このページ内のみ。これのsetupのiteration版がiratef_lemma_refとなっている。
-- fも使ってないので、行き先が一つとは限らない。
--path_exists_setupを経由してやや冗長ではあるが、順序をカバー関係に分解する必要があるので、書き直してもそれほど短くならないかも。
lemma path_exists {α : Type} [Fintype α] (R : α → α → Prop) (x y : α) (h : Relation.ReflTransGen R x y) :
  ∃ (n : ℕ) (z : Fin (n + 1) → α), z 0 = x ∧ z n = y ∧ ∀ i : Fin n, R (z i.castSucc) (z i.succ) := by
  -- ReflTransGen の帰納法を適用
  induction h
  case refl x =>
    -- x = y の場合は n=0 の列を取る
    exists 0
    let z : Fin (0+1) → α := fun _ => x
    exists z
    constructor
    · rfl
    constructor
    · rfl
    -- 長さ0のときは「次がある i : Fin 0」は存在しないので仮定矛盾 (vacuous truth)
    · intro i
      cases i
      simp_all only [Nat.reduceAdd, Fin.castSucc_mk, Fin.succ_mk, z]
      simp_all only [not_lt_zero']

  case tail b c h₁ h₂ ih =>
    -- 推移的ケース: x から b に到達し、さらに b から c に R で到達
    rcases ih with ⟨n, z, hz₀, hzn, hR⟩  -- 帰納法の仮説から n, z を取り出す
    use n + 1  -- 新しいパス長は n + 1
    use fun i : Fin (n + 2) => if h : ↑i ≤ n then z ⟨i.val, Nat.lt_succ_of_le h⟩ else c
    constructor
    ·
      subst hz₀ hzn
      simp_all only [Fin.natCast_eq_last, Fin.val_zero, zero_le, ↓reduceDIte, Fin.zero_eta]
    constructor
    · have : ↑(Fin.last (n + 1)) = n + 1 := rfl
      simp [this, hzn]
      --simp [Nat.not_le.mpr (Nat.lt_succ_self n)]
      intro h
      have : n.succ ≤ n := by
        convert h
        subst hz₀ hzn
        simp_all only [Fin.natCast_eq_last, Nat.succ_eq_add_one]
        simp [Fin.val_add]
      exact False.elim (Nat.not_succ_le_self n this)

    · intro i
      simp [Fin.castSucc, Fin.succ]
      split_ifs with h₁ h₂
      ·
        rename_i h₂_1
        subst hz₀ hzn
        simp_all only [Fin.natCast_eq_last]
        have h₁_2 := h₂_1
        simp_all only
        exact hR ⟨i, h₂⟩
      · have : i = Fin.last n := by
          apply Fin.ext
          rw [Fin.val_last]

          apply Nat.eq_of_le_of_lt_succ
          subst hz₀ hzn
          simp_all only [not_le, Fin.natCast_eq_last]
          omega
          subst hz₀ hzn
          simp_all only [not_le, Fin.natCast_eq_last, Fin.is_lt]
        --rw [this, Fin.castSucc_last, hzn]
        subst this hz₀ hzn
        simp_all only [Fin.val_last, not_le, Fin.natCast_eq_last]
      · apply absurd h₁ -- i ≤ n だが i + 1 ≤ n でない場合、矛盾
        rename_i h₁_1 h
        subst hz₀ hzn
        simp_all only [not_le, Fin.natCast_eq_last, not_true_eq_false]
        revert h₁_1
        intro h₁_1
        exact h₁.not_lt h
      · apply absurd h₁ --h₂  -- i ≤ n でない場合も矛盾（i : Fin (n + 1) の範囲による）
        rename_i h₁_1 h
        subst hz₀ hzn
        simp_all only [not_le, Fin.natCast_eq_last, not_true_eq_false]
        have h₂ := h₁_1
        simp_all only
        have := h₂
        simp_all only
        revert this
        intro this
        cases i
        simp_all only
        omega




--補題 頂点aから頂点bにfのパスで辿れるときは、a <= bである。
--外ファイルからの参照はない。
lemma path_implies_le {α : Type} [Fintype α] [DecidableEq α] (s : Setup α) (a b : {x // x ∈ s.V}) :
  (∃ (n : ℕ) (z : Fin (n + 1) → {x // x ∈ s.V}), z 0 = a ∧ z n = b ∧ ∀ i : Fin n, s.f (z i.castSucc) = (z i.succ)) → s.pre.le a b :=
by

  intro h
  rcases h with ⟨n, z, hz₀, hzn, hstep⟩

  -- パスの長さ n による帰納法で ReflTransGen を構成
  induction n generalizing a --aをgeneralizingしたことがポイント。ihを使う時にaを設定できる。
  case zero =>
    -- 長さ0のとき：z 0 = a = z n = b より a = b
    subst hzn hz₀
    simp_all only [IsEmpty.forall_iff, Fin.isValue, Nat.reduceAdd, Nat.cast_zero, le_refl]

  case succ n ih =>
    -- z : Fin (n + 2) → _, z 0 = a, z (n+1) = b
    let a' := z 0
    let b' := z 1
    have h₁ : s.pre.le a' b' :=
    by
      exact f_and_pre s a' b' (hstep 0)

    -- 部分列 z' : Fin (n + 1) → {x // x ∈ s.V}, i ↦ z (i.succ)
    let z' : Fin (n + 1) → {x // x ∈ s.V} := fun i => z (i+1)

    -- z' 0 = b', z' n = b
    have h₀' : z' 0 = b' := rfl
    have hn' : z' n = b := by

      dsimp [z']
      subst hz₀ hzn
      simp_all only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_zero_eq_one, Fin.natCast_eq_last,
        Nat.cast_add, Nat.cast_one, Nat.mod_succ, z', a', b']

    -- 各ステップで le が成り立つ
    have hstep' : ∀ i : Fin n, s.pre.le (z' i.castSucc) (z' i.succ) := by
      intro i
      -- z' i.castSucc = z i.succ, z' i.succ = z i.succ.succ
      -- よって hstep (i.succ)
      subst hn' hz₀
      simp_all only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_zero_eq_one, Nat.cast_add, Nat.cast_one,
        Fin.natCast_eq_last, Fin.succ_last, Nat.succ_eq_add_one, a', z', b']
      obtain ⟨val, property⟩ := a'
      obtain ⟨val_1, property_1⟩ := b'
      apply f_and_pre s
      ext : 1
      congr
      exact hstep i.succ

    -- 帰納法の仮定に適用
    let ihz := ih b' z' h₀' hn'
    have :(∀ (i : Fin n), s.f (z' i.castSucc) = z' i.succ) := by
      intro i
      let hstepi := hstep i
      subst hn' hz₀
      simp_all only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last,
        Fin.succ_last, Nat.succ_eq_add_one, a', b', z']
      obtain ⟨val, property⟩ := a'
      obtain ⟨val_1, property_1⟩ := b'
      rw [Fin.succ_castSucc]
      simp_all only [z']
    specialize ihz this
    have : s.pre.le a' b := s.pre.le_trans a' b' b h₁ ihz
    have : s.pre.le a b := by
      subst hn' hz₀
      simp_all only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_zero_eq_one, Fin.natCast_eq_last,
        Fin.succ_last, Nat.succ_eq_add_one, Subtype.forall, Nat.cast_add, Nat.cast_one, b', z', a']
    exact this

--証明できたけど、写像が後ろから前に向かっているので逆になっている。外からは使わないけど、次の補題で使っている。
--外ファイルからの参照なし。
lemma path_exists_setup_reverse (s: Setup α) (x y : {x : α // x ∈ s.V}) :
  s.pre.le x y →
  ∃ (n : ℕ) (z : Fin (n + 1) → {x : α // x ∈ s.V}), z 0 = y ∧ z n = x ∧ ∀ i : Fin n, (z i.castSucc) = s.f (z i.succ) :=
by
  intro h
  let R := R_from_RS1 (rootedset_from_setup s)
  have h' : @Relation.ReflTransGen s.V R y x := by
    exact (size_one_preorder_setup_lemma s x y).mp h
  dsimp [R] at h'
  let pe := path_exists (R_from_RS1 (rootedset_from_setup s)) y x h'
  obtain ⟨n, z, hz₀, hzn, hstep⟩ := pe
  use n, z
  constructor
  · exact hz₀
  constructor
  · exact hzn
  · intro i
    specialize hstep i
    let sop := size_one_preorder_setup_step s (z i.succ) (z i.castSucc)
    rw [sop] at hstep
    subst hzn hz₀
    simp_all only [Fin.natCast_eq_last, R]

--大小関係はfの繰り返しで書けること。
--外からは参照なし。中からは使っている。
--eqClass_size_ge_two_implies_outsideとiteratef_lemma_refで使っている。
--このなかでpath_exists_setup_reverseを使っている。
--fを使ってないアプローチなので浮いているかも。ファイル外からは参照されていない。
--eqClass_size_ge_two_implies_outsideで参照されている。
--大小関係があるときは、fの適用の繰り返してかけるというように書き直すことが可能。
--リファクタリングのためには、reachで言明を書き換えたい。
lemma path_exists_setup (s: Setup α) (x y : {x : α // x ∈ s.V}) :
  s.pre.le x y →
  ∃ (n : ℕ) (z : Fin (n + 1) → {x : α // x ∈ s.V}), z 0 = x ∧ z n = y ∧ ∀ i : Fin n, s.f (z i.castSucc) = (z i.succ) :=
by
  intro h
  obtain ⟨n, z, hz0, hzn, hzstep⟩ := path_exists_setup_reverse s x y h
  let w : Fin (n + 1) → {x : α // x ∈ s.V} := fun i => z ⟨n - i, by
  subst hzn hz0
  simp_all only [Fin.natCast_eq_last]
  omega⟩
  use n, w
  have hw0 : w 0 = x := by
    subst hzn hz0
    simp_all only [Fin.val_zero, tsub_zero, Fin.natCast_eq_last, w]
    rfl
  have hwn : w n = y := by
    subst hzn hz0
    simp_all only [Fin.val_zero, tsub_zero, Fin.natCast_eq_last, Fin.val_last, tsub_self, Fin.zero_eta, w]
  constructor
  · exact hw0
  constructor
  · exact hwn
  · intro i
    have hw: w i.castSucc = z ⟨n - i.castSucc, _⟩ := rfl
    have : w i.succ = z ⟨n - i.succ, _⟩ := rfl
    rw [this]
    rw [hw]
    simp
    --show s.f (z ⟨n - ↑i, ⋯⟩) = z ⟨n - (↑i + 1), ⋯⟩

    have : 0 < n:= by
      subst hzn hz0
      simp_all only [Fin.val_zero, tsub_zero, Fin.natCast_eq_last, Fin.val_last, tsub_self, Fin.zero_eta, w]
      contrapose! hw0
      simp_all only [nonpos_iff_eq_zero, Fin.zero_eta, ne_eq, w]
      subst hw0
      simp_all only [IsEmpty.forall_iff, Fin.isValue, Fin.last_zero, not_true_eq_false]
      fin_cases i
    by_cases hi: i = ⟨0, this⟩
    case pos =>
      subst hi
      simp
      subst hzn hz0
      simp_all only [Fin.val_zero, tsub_zero, Fin.natCast_eq_last, Fin.val_last, tsub_self, Fin.zero_eta, w]
      rw [←hw0]
      have : n - 1 < n:= by
        simp_all only [tsub_lt_self_iff, Nat.lt_one_iff, pos_of_gt, and_self, w]
      specialize hzstep ⟨n-1, this⟩
      simp_all only [Fin.castSucc_mk, Fin.succ_mk, w]
      congr
      ext : 1
      simp_all only [Fin.val_last, w]
      omega

    case neg =>
      have : n - i.castSucc - 1 < n := by
        subst hzn hz0
        simp_all only [Fin.val_zero, tsub_zero, Fin.natCast_eq_last, Fin.val_last, tsub_self, Fin.zero_eta,
          Fin.coe_castSucc, Fin.val_succ, w]
        omega
      let hzs := hzstep ⟨n - i.castSucc - 1, this⟩
      simp at hzs
      ring_nf
      ring_nf at hzs
      symm
      have :1 + (n - (@Fin.val n i : ℕ) - 1) = n - (@Fin.val n i : ℕ) := by
        subst hzn hz0
        simp_all only [Fin.val_zero, tsub_zero, Fin.natCast_eq_last, Fin.val_last, tsub_self, Fin.zero_eta, w]
        omega
      simp_all only [Fin.castSucc_mk, Fin.succ_mk, w]
      rw [←hzs]
      congr 1
      subst hzn hz0
      simp_all only [Fin.val_zero, tsub_zero, Fin.natCast_eq_last, Fin.val_last, tsub_self, Fin.zero_eta,
        Fin.mk.injEq]
      rw [add_comm]
      rfl

--補題。上の補題は、途中のノードに対しても成り立つこと。
--ファイル内から参照。eqClass_size_ge_two_implies_outsideから。
lemma path_implies_front {α : Type} [Fintype α] [DecidableEq α] (s : Setup α) (a : {x // x ∈ s.V})
  (n : ℕ) (z : Fin (n + 1) → {x // x ∈ s.V})
  (h0 : z 0 = a) --(hn : z n = b)
  (h : ∀ i : Fin n, s.f (z i.castSucc) = (z i.succ)) :
  ∀ ii : Fin n, s.pre.le a (z ii.castSucc) :=
by
  intro ii
  -- Show that from a to z ii.castSucc there is a path
  apply path_implies_le s a (z ii.castSucc)
  use ii
  let z' : Fin (ii + 1) → {x // x ∈ s.V} := fun i => z i
  have h': ∀ (i : Fin ii), s.f (z' i.castSucc) = z' i.succ :=
  by
    intro i
    dsimp [z']
    have np1: i < n := by
      subst  h0
      omega
    let i' : Fin (n) := ⟨i.val, np1⟩
    have h_i' : z i'.castSucc = z' i.castSucc := by
      simp [z', Fin.castSucc]
      subst  h0
      simp_all only [z', i']
      congr
      simp_all only [Fin.castAdd_mk, z', i']
      ext : 1
      simp_all only [Fin.val_natCast, z', i']
      symm
      simp_all only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, z', i']
      linarith
    have h_succ : z i'.succ = z' i.succ := by
      simp [z', Fin.succ]
      subst  h0
      simp_all only [Fin.castSucc_mk, Fin.coe_castSucc, z', i']
      ext : 1
      congr
      simp_all only [Nat.add_mod_mod, Nat.mod_add_mod, z', i']
      rw [Nat.mod_eq_of_lt (Nat.succ_le_succ np1)]
    subst  h0
    simp_all only [Fin.castSucc_mk, Fin.coe_castSucc, Fin.succ_mk, Fin.val_succ, Nat.cast_add, Nat.cast_one, z', i']
    specialize h i'
    simp_all only [Fin.castSucc_mk, Fin.succ_mk, z', i']
  subst  h0
  simp_all only [Fin.coe_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, z']
  use z'
  simp_all only [Fin.val_zero, Nat.cast_zero, Fin.val_last, Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.val_succ,
    Nat.cast_add, Nat.cast_one, implies_true, and_self, z']

--後ろで使っている。eqClass_size_ge_two_implies_inverse
lemma path_implies_rear {α : Type} [Fintype α] [DecidableEq α] (s : Setup α) (b : {x // x ∈ s.V})
  (n : ℕ) (z : Fin (n + 1) → {x // x ∈ s.V})
  --(h0 : z 0 = a)
  (hn : z n = b)
  (h : ∀ i : Fin n, s.f (z i.castSucc) = (z i.succ)) :
  ∀ ii : Fin n, s.pre.le (z ii.castSucc) b:=
by
  intro ii
  -- Show that from z ii.castSucc to b there is a path
  apply path_implies_le s (z ii.castSucc) b
  use n - ii.val
  let z' : Fin (n - ii.val + 1) → {x // x ∈ s.V} := fun i => z (i + ii.val)
  have h': ∀ (i : Fin (n - ii.val)), s.f (z' i.castSucc) = z' i.succ :=
  by
    intro i
    dsimp [z']
    have np1: i + ii.val < n := by
      subst hn
      omega
    let i' : Fin (n) := ⟨i.val + ii.val, np1⟩
    have h_i' : z i'.castSucc = z' i.castSucc := by
      simp [z', Fin.castSucc]
      subst hn
      simp_all only [z', i']
      congr
      simp_all only [Fin.castAdd_mk, z', i']
      ext : 1
      simp_all only [Fin.val_natCast, z', i']
      symm
      rw [Fin.val_add]
      simp_all only [Fin.val_natCast, Fin.coe_castAdd, Nat.mod_add_mod, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
        z', i']
      linarith
    have h_succ : z i'.succ = z' i.succ := by
      simp [z', Fin.succ]
      subst hn
      simp_all only [Fin.castSucc_mk, Fin.coe_castSucc, z', i']
      ext : 1
      congr
      simp_all only [Nat.add_mod_mod, Nat.mod_add_mod, z', i']
      have :(↑i + 1 + ↑ii) < n + 1 := by
        simp_all only [Fin.coe_eq_castSucc, z', i']
        linarith
      simp_all only [Fin.coe_eq_castSucc, z', i']
      rw [Nat.mod_eq_of_lt this]
      ring
    subst hn
    simp_all only [Fin.castSucc_mk, Fin.coe_castSucc, Fin.succ_mk, Fin.val_succ, Nat.cast_add, Nat.cast_one, z', i']
    specialize h i'
    simp_all only [Fin.castSucc_mk, Fin.succ_mk, z', i']
  subst hn
  simp_all only [Fin.coe_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, z']
  use z'
  simp_all only [Fin.coe_eq_castSucc, z']
  simp_all only [Fin.val_zero, Nat.cast_zero, zero_add, Fin.val_last, Fin.is_le', Nat.cast_sub,
    Fin.natCast_eq_last, Fin.coe_eq_castSucc, sub_add_cancel, Fin.coe_castSucc, Fin.val_succ,
    Nat.cast_add, Nat.cast_one, implies_true, and_self, z']


--補題。サイズ2以上の同値類は、fの行き先が同値類の外にでない。
--後ろで使っている。f_on_equivなどで参照されている。外からは使っていない。
--iterationでなく、pathで証明されている。この証明をPathを使わずにiteration系の補題から証明したい。
--=>上に書き直した。
lemma eqClass_size_ge_two_implies_outside2
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α):
    ∀ y : {x // x ∈ s.V}, ( 2 ≤ (eqClass_setup s y).card) → s.f y ∈ (eqClass_setup s y):=
by
  intro y h
  let eqy := eqClass_setup s y
  have : eqy \ {y} ≠ ∅ := by
    simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, eqy]
    obtain ⟨val, property⟩ := y
    apply And.intro
    · apply Aesop.BuiltinRules.not_intro
      intro a
      simp_all only [Finset.card_empty, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero]
    · apply Aesop.BuiltinRules.not_intro
      intro a
      simp_all only [Finset.card_singleton, Nat.not_ofNat_le_one]

  have : (eqy \ {y}).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact this
  obtain ⟨z, hz⟩ := this
  have : s.pre.le y z := by
    dsimp [eqy] at hz
    apply eqClass_le
    simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, mem_sdiff,
      Finset.mem_singleton, eqy]

  obtain ⟨n , zz , hz0, hz1, hhz⟩ := path_exists_setup s y z this
  have prezy:(s.pre.le z y) := by
    dsimp [eqy] at hz
    dsimp [eqClass_setup] at hz
    rw [s.h_setoid] at hz
    dsimp [setoid_preorder] at hz
    simp at hz
    have : s.pre.le z y := by
      dsimp [AntisymmRel] at hz
      subst hz1 hz0
      simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.natCast_eq_last,
        true_and, eqy]
    subst hz1 hz0
    simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.natCast_eq_last, eqy]
  have : s.pre.le y (s.f y)  := by
    have le1: 1 <= n := by
      rename_i this_1
      subst hz1 hz0
      simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.natCast_eq_last,
        mem_sdiff, Finset.mem_singleton, eqy]
      obtain ⟨left, right⟩ := this_1
      obtain ⟨left_1, right_1⟩ := hz
      contrapose! right_1
      simp_all only [Nat.lt_one_iff]
      subst right_1
      simp_all only [IsEmpty.forall_iff, Fin.isValue, Fin.last_zero, le_refl]
    by_cases n = 1
    case pos =>
      exact f_and_pre s y (s.f y) rfl
    case neg =>
      have : 1 < n := by
        subst hz1 hz0
        simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.natCast_eq_last,
          mem_sdiff, Finset.mem_singleton, eqy]
        rename_i this_2
        obtain ⟨left, right⟩ := this_2
        obtain ⟨left_1, right_1⟩ := hz
        omega
      let pi := path_implies_front s y n zz hz0 hhz ⟨1, this⟩
      have :zz (⟨1, this⟩:Fin n).castSucc = s.f y := by
        have : 0 < n:= by
          rename_i this_1 this_2 h_1
          subst hz1 hz0
          simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.natCast_eq_last,
            mem_sdiff, Finset.mem_singleton, eqy]
          obtain ⟨left, right⟩ := this_1
          obtain ⟨left_1, right_1⟩ := hz
          exact le1
        let hhz0 := hhz (⟨0, this⟩:Fin n)
        simp
        rw [←hz0]
        rename_i this_1 this_2 h_1 this_3
        subst hz1 hz0
        simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.natCast_eq_last,
          mem_sdiff, Finset.mem_singleton, eqy]
        obtain ⟨left, right⟩ := this_1
        obtain ⟨left_1, right_1⟩ := hz
        exact hhz0.symm
      rename_i this_1 this_2 h_1 this_3
      subst hz1 hz0
      simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.castSucc_mk,
        Fin.natCast_eq_last, mem_sdiff, Finset.mem_singleton, ge_iff_le, eqy]
      obtain ⟨left, right⟩ := this_1
      obtain ⟨left_1, right_1⟩ := hz
      rw [← this]
      exact pi

  have : s.pre.le (s.f y) z := by
    -- Add proof for the equality here

    --s.pre.le y (s.f y) のケースと似ているが、こちらは、path_implies_rearを使う。
    have : 0 < n:= by
      rename_i this_1 this_2 h_1
      subst hz1 hz0
      simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.natCast_eq_last,
        mem_sdiff, Finset.mem_singleton, eqy]
      obtain ⟨left_1, right_1⟩ := hz
      obtain ⟨left, right⟩ := this_2
      apply Nat.pos_of_ne_zero
      simp_all only [ne_eq, eqy]
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [IsEmpty.forall_iff, Fin.isValue, Fin.last_zero, le_refl, not_true_eq_false]
    by_cases n = 1
    case pos =>
      let hhz0 := hhz ⟨0, this⟩
      have : s.f y = z := by
        -- Add proof for the equality here
        rename_i this_1 this_2 this_3 h_1
        subst hz1 h_1 hz0
        simp_all only [Fin.isValue, ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or,
          Nat.reduceAdd, Nat.cast_one, mem_sdiff, Finset.mem_singleton, eqy]
        obtain ⟨left, right⟩ := this_1
        obtain ⟨left_1, right_1⟩ := hz
        exact hhz0
      rename_i h_1
      subst this h_1 hz0
      simp_all only [Fin.isValue, ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, mem_sdiff,
        Finset.mem_singleton, Nat.reduceAdd, Nat.cast_one, le_refl, eqy]
    case neg =>
    have geq1: 1 < n := by
      subst hz1 hz0
      simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.natCast_eq_last,
        mem_sdiff, Finset.mem_singleton, eqy]
      rename_i this_1
      rename_i this_3
      obtain ⟨left, right⟩ := this_3
      obtain ⟨left_1, right_1⟩ := hz
      omega

    let pi := path_implies_rear s z n zz hz1 hhz ⟨1, geq1⟩ --zzは、Fin n+1で定義されている。
    have :zz (⟨1, geq1⟩:Fin n).castSucc = s.f y := by

      let hhz0 := hhz (⟨0, this⟩:Fin n)
      simp
      rw [←hz0]
      rename_i this_1 this_2 h_1 this_3
      subst hz1 hz0
      simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.natCast_eq_last,
        mem_sdiff, Finset.mem_singleton, eqy]
      obtain ⟨left_1, right_1⟩ := hz
      exact hhz0.symm

    have :zz (⟨1, geq1⟩:Fin n).castSucc = s.f y := by
      have : 0 < n:= by --上でも証明しているので無駄。
        rename_i this_1 this_2 h_1
        subst hz1 hz0
        simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.natCast_eq_last,
          mem_sdiff, Finset.mem_singleton, eqy]
      let hhz0 := hhz (⟨0, this⟩:Fin n)
      simp
      rw [←hz0]
      rename_i this_1 this_2 h_1 this_3
      subst hz1 hz0
      simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.natCast_eq_last,
        mem_sdiff, Finset.mem_singleton, eqy]
      obtain ⟨left_1, right_1⟩ := hz
      exact hhz0.symm
    have :zz (⟨1, geq1⟩:Fin n).castSucc = s.f y := by
      subst hz1 hz0
      simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.castSucc_mk,
        Fin.natCast_eq_last, mem_sdiff, Finset.mem_singleton, eqy]
    rw [←this]
    exact pi

  have : s.pre.le (s.f y) y := by
    -- s.pre.le (s.f y) zとs.pre.le z yの推移律を使う。
    exact s.pre.le_trans  (s.f y) z y this prezy

  dsimp [eqClass_setup]
  rw [Finset.mem_filter]
  constructor
  · simp
  · rw [s.h_setoid]
    dsimp [setoid_preorder]
    rename_i this_1 hz_1 this_2 this_3 this_4
    subst hz1 hz0
    simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, Fin.natCast_eq_last,
      mem_sdiff, Finset.mem_singleton, eqy]
    obtain ⟨left_1, right_1⟩ := hz_1
    constructor
    · simp_all only
    · simp_all only

----Setup前提の極大


--このファイルのメイン定理のひとつ. Setup前提。サイズが2以上の同値類は、極大要素になること。
--サイズ2以上の同値類からいけるところは、同じ同値類内に必ずなる。このことは前の補題で示されている。
--pathexsits_setupを使っているが、パスの議論をやめて、fの繰り返しで書けることに書き換えた方がいいかも。
--この定理は、functionalSPOのeqClass_Maximalで使われる。それは、同値類の極大性の定理。
--pathでなく、reachを使って、o3で書き直そうと思う。手で直すこともできるかも。
--path_exists_setupとeqClass_size_ge_two_implies_outsideとpath_implies_rearを使っている。
theorem eqClass_size_ge_two_implies_inverse2
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α)
    (x : {x // x ∈ s.V})
    (h : 2 ≤ (eqClass_setup s x).card) :
    isMaximal s x := by
  --∀ y : {x // x ∈ s.V},  s.pre.le x y → s.pre.le y x := by
  intro y h_xy
  obtain ⟨n,z,hz0,hz1,hz⟩ :=  path_exists_setup s x y h_xy --zはFin n+1で定義されている。

  induction n generalizing x
  case zero =>
    have : x = y:= by
      subst hz0 hz1
      simp_all only [IsEmpty.forall_iff, Fin.isValue, mem_attach, AntisymmRel.setoid_r, true_and, Nat.reduceAdd,
        Nat.cast_zero, le_refl]
    subst hz0 this
    simp_all only [IsEmpty.forall_iff, Fin.isValue, mem_attach, AntisymmRel.setoid_r, true_and, Nat.reduceAdd,
      Nat.cast_zero, le_refl]
  case succ nn ih => --zはFin nn+1+1で定義されている。これでいいのか？
    have hn : nn + 1 ≥ 1 := Nat.succ_le_succ (Nat.zero_le nn)

    have : s.f x ∈ eqClass_setup s x := by
      apply eqClass_size_ge_two_implies_outside s x h

    have slex1: s.pre.le (s.f x) x := by
      apply eqClass_ge s x (s.f x) this

    have slex2: s.pre.le x (s.f x) := by
      exact f_and_pre s x (s.f x) rfl

    let ihh := ih (s.f x)

    have : eqClass_setup s x = eqClass_setup s (s.f x) := by
      apply eqClass_eq s x (s.f x) slex2 slex1

    have : 2 ≤ (eqClass_setup s (s.f x)).card := by
      rw [this] at h
      exact h

    specialize ihh this

    have : s.pre.le (s.f x) y := by

      by_cases nn = 0
      case pos =>
        subst hz0 hz1
        simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, eqClass_setup]
        rename_i h this_2 this_3
        subst h
        simp_all only [zero_add, ge_iff_le, le_refl, lt_self_iff_false]
        --show s.f (z 0) ≤ z ↑1
        have : 0 < 1 := by
          exact Nat.one_pos
        let hz0 := hz ⟨0, this⟩
        simp at hz0
        rw [hz0]
        simp_all only [Fin.isValue, mem_filter, mem_attach, true_and, Nat.reduceAdd, Nat.cast_one, Nat.cast_zero,
          IsEmpty.forall_iff, le_refl, imp_self, implies_true, hz0]

      case neg =>
        have : 1 < nn+1:= by
          subst hz0 hz1
          simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, eqClass_setup]
          simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, mem_filter, mem_attach, true_and, Nat.cast_add,
            Nat.cast_one, Fin.natCast_eq_last, Subtype.forall, Subtype.coe_eta, lt_add_iff_pos_left]
          positivity

        let pi := path_implies_rear s y (nn+1) z hz1 hz ⟨1, this⟩ --zzは、Fin n+2で定義されている。
        have :z (⟨1, this⟩:Fin (nn+1)).castSucc = s.f x := by
          let hhz0 := hz (⟨0, hn⟩:Fin (nn+1))
          simp
          rw [←hz0]
          rename_i this_1 this_2 h_1 this_3
          subst hz1 hz0
          simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, eqClass_setup]
          exact hhz0.symm
        rw [←this]
        exact pi
    --ここまでで、s.pre.le (s.f x) yが示されたので、ihhを利用することができる。
    specialize ihh this
    let zz' : Fin (nn+1) → {x // x ∈ s.V} := fun i => z (i + 1)  --ここでFin (nn+1)にするのはあっているのか。zはFin (nn+2)が定義域。
    specialize ihh zz'
    have : 0 < nn + 1:= by
      subst hz1 hz0
      simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last,
        Subtype.forall, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_zero_eq_one, Fin.succ_last,
        Nat.succ_eq_add_one, Subtype.coe_eta, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true,
        zz']--nn=0の場合を別扱いする必要があるかも。
    have : zz' 0 = s.f x := by
      dsimp [zz']
      symm
      simp
      let hhz1 := hz ⟨0, this⟩
      subst hz1 hz0
      simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last,
        Subtype.forall, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_zero_eq_one, Fin.succ_last,
        Nat.succ_eq_add_one, Subtype.coe_eta, zz']
      exact hhz1
    specialize ihh this
    have :zz' ↑nn = y := by
      dsimp [zz']
      subst hz1 hz0
      simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff,
        pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall, Fin.coe_eq_castSucc,
        Fin.coeSucc_eq_succ, Fin.succ_zero_eq_one, Fin.succ_last, Nat.succ_eq_add_one, Subtype.coe_eta, Nat.mod_succ,
        zz']
    specialize ihh this
    have :(∀ (i : Fin nn), s.f (zz' i.castSucc) = zz' i.succ) := by
      intro i
      dsimp [zz']
      have : i + 1 < nn + 1:= by
        subst hz1 hz0
        simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff,
          pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall, Fin.coe_eq_castSucc,
          Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one, Subtype.coe_eta,
          add_lt_add_iff_right, Fin.is_lt, zz']
      let hzz := hz ⟨(i + 1),this⟩
      --hzは、Fin nn+1が定義域であり、0からnnの値まで定義されている。ここでのiは、0からnn-1までなので溢れてはいない。
      --ゴールのs.f (z (↑↑i + 1)) = z (↑(↑i + 1) + 1)は、Fin (nn +2)で定義されてしまっている。これはおかしい？
      -- ここで、iがnnに達する場合の処理を追加する必要があるかもしれない。

      by_cases hi:i = nn --iがnnになることはない気がするのでいらないかも。Fin nnでは、ii= 0のとき。
      case pos =>
        simp at hzz
        have : i = Fin.mk 0 (Nat.zero_lt_of_ne_zero (by
          subst hz1 hz0
          simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff,
            pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall, Fin.coe_eq_castSucc,
            Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one, Subtype.coe_eta, ne_eq, zz']
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [Nat.reduceAdd, Nat.cast_zero, Fin.isValue, zero_add, Fin.last_zero, IsEmpty.forall_iff,
            le_refl, imp_self, implies_true, Fin.reduceLast]
          linarith)):= by
            subst hz1 hz0
            simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff,
              pos_of_gt, or_true, zz']
            simp [hi] at this
            rename_i this_1 this_2 this_3 this_4 this_5 this_6 this_7
            simp at this_1
            simp_all only [zz']
            ext : 1
            simp_all only [zz']
            simp_all only [Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall, Fin.coe_eq_castSucc,
              Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one, Subtype.coe_eta, zz']
            omega

        simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff,
          pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall, Fin.coe_eq_castSucc,
          Fin.coeSucc_eq_succ, Fin.succ_zero_eq_one, Fin.succ_last, Nat.succ_eq_add_one, Subtype.coe_eta, zz']
        --show s.f (z (↑nn + 1)) = z (↑nn + 1 + 1)
        subst hz1 hz0
        simp_all only [Nat.cast_zero, zero_add, zz']
        exfalso
        linarith

      case neg =>
        by_cases hn0:i = nn - 1 --これは場合分けする必要がある。i.succがFin nnだと0になる。
        case pos =>
          rw [hn0]
          simp
          suffices s.f (z nn) = z (nn + 1) from by

            have :(((↑(nn - 1):Fin (nn+2)) + 1):Fin (nn+2)) = (nn:Fin (nn+2)):= by
              apply Fin.mk.inj_iff.mpr

              simp
              ring_nf
              subst hz1 hz0
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff,
                Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall,
                Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one,
                Subtype.coe_eta, zz']
              rw [add_comm]
              rw [tsub_add_cancel_of_le (by omega)]

            rw [this]
            have : ((↑nn + 1):Fin (nn+2)) = ↑(nn - 1) + 1 + 1 := by
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff,
                Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall,
                Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one,
                Subtype.coe_eta, zz']
            rw [this]
            subst hz1 hz0
            simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff,
              Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall,
              Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one,
              Subtype.coe_eta, zz']

          have : nn < nn + 1:=
            by
              omega
          let hzn := hz ⟨nn, this⟩
          have : nn < nn + 2 :=
            by
              omega
          change s.f (z ⟨nn,this⟩) = z ⟨nn + 1,by simp⟩ at hzn
          convert hzn
          · subst hz1 hz0
            simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff,
              pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall, Fin.coe_eq_castSucc,
              Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one, Subtype.coe_eta,
              Fin.val_natCast, Nat.mod_succ_eq_iff_lt, zz']
          · rw [Fin.val_add_one]
            split
            · rename_i h
              have :(@Nat.cast (Fin (nn + 1 + 1)) Fin.instNatCast nn : Fin (nn + 1 + 1)) = (Fin.last (nn + 1) : Fin (nn + 1 + 1))  :=
                by
                  subst hz1 hz0
                  simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff,
                    Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.last_add_one,
                    Fin.natCast_eq_last, Subtype.forall, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_last,
                    Nat.succ_eq_add_one, Subtype.coe_eta, Fin.succ_zero_eq_one, le_refl, implies_true, zz']
              have : (↑nn : ℕ) = (Fin.last (nn + 1)).val := by
                simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff,
                  Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.last_add_one,
                  Fin.natCast_eq_last, Subtype.forall, Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_last,
                  Nat.succ_eq_add_one, Subtype.coe_eta, Fin.succ_zero_eq_one, le_refl, implies_true, zz']
                rw [←this]
                apply Eq.symm
                apply  Fin.val_cast_of_lt
                simp_all only [Subtype.coe_eta, zz']
              -- ↑nn = nn, Fin.last (nn + 1) = nn + 1
              rw [Fin.val_last] at this
              exact Eq.symm ((fun {n} => Nat.eq_self_sub_one.mp) (id (Eq.symm this)))
            ·
              subst hz1 hz0
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff,
                Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall,
                Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one,
                Subtype.coe_eta, Fin.val_natCast, add_left_inj, Nat.mod_succ_eq_iff_lt, zz']

        case neg =>

          convert hzz

          · dsimp [Fin.castSucc]
            apply Fin.ext
            simp
            set ii := i.val with hii

            suffices (↑((↑ii + 1):Fin (nn + 2))) = ii + 1 from by
              exact this

            have :↑ii + 1 < nn + 2 := by
              subst hz1 hz0
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left,
                add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one,
                Fin.natCast_eq_last, Subtype.forall, Subtype.coe_eta, add_lt_add_iff_right, zz']
              linarith
            let fmt := Fin.val_mk this
            rw [←fmt]
            have hii:ii < nn + 2:= by
              subst hz1 hz0
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff,
                Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall,
                Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one,
                Subtype.coe_eta, zz', ii]
              linarith
            have hh:ii + 1 < nn + 2 := by
              simp_all [zz', ii]

            --これは両辺同じもの。
            have : (⟨(⟨ii,hii⟩:Fin (nn + 2)) + 1, hh⟩:Fin (nn+2)) = ⟨ii + 1, hh⟩ := by
              subst hz1 hz0
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff,
                Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall,
                Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one,
                Subtype.coe_eta, zz', ii]
            rw [this]
            simp
            dsimp [Nat.cast]
            dsimp [NatCast.natCast]

            have :(@Fin.val (nn + 2) (↑ii + 1) : ℕ) = ii + 1 := by
              have : (((↑ii:Fin (nn+2))+ 1) :Fin (nn+2)) = ⟨ii + 1, hh⟩ := by
                have h1 : (↑ii : Fin (nn + 2)) = ⟨ii, hii⟩ := by
                  apply Fin.ext
                  simp_all [ii]
                -- 加算の定義を展開：(ii + 1) % (nn + 2)
                have h2 : (ii + 1) % (nn + 2) = ii + 1 := by
                  apply Nat.mod_eq_of_lt
                  exact hh
                -- 加算結果を計算
                have h3 : (⟨ii, hii⟩ : Fin (nn + 2)) + 1 = ⟨ii + 1, hh⟩ := by
                  rw [Fin.add_def]  -- Fin の加算定義を使用
                  exact Fin.mk.inj_iff.mpr h2
                -- 値が等しいことを確認
                /- --両辺同じに見える。不要。
                have h4 : (⟨ii + 1, hh⟩ : Fin (nn + 2)) = ⟨ii + 1, hh⟩ := by
                  apply Fin.ext  -- Fin の値が等しいことを示す
                  rfl            -- 値はともに ii + 1
                -/
                -- 全てを組み合わせる
                rw [h1, h3]
              subst hz1 hz0
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left,
                add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one,
                Fin.natCast_eq_last, Subtype.forall, Subtype.coe_eta, zz', ii]
            exact this

          · subst hz1 hz0
            simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left,
              add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one,
              Fin.natCast_eq_last, Subtype.forall, Subtype.coe_eta, Fin.succ_mk, zz']
            apply Fin.ext
            set ii := i.val with hhi
            have hii: ii + 2 < nn + 2 := by
              dsimp [ii]
              simp_all only [Subtype.coe_eta, add_lt_add_iff_right, Fin.is_lt, zz']
            have hiii:ii < nn + 2:= by
              simp_all only [Subtype.coe_eta, add_lt_add_iff_right, Fin.is_lt, ii, zz']
              linarith
            have hiiii:ii + 1 < nn + 1 := by
              linarith
            suffices ↑((↑ii:Fin (nn+2)) + 1+1) = ↑⟨ii + 1+1,hii⟩ from by
              dsimp [ii]
              dsimp [ii] at this
              rw [this]

            have h1 : (↑ii : Fin (nn + 2)) = ⟨ii, hiii⟩ := by
              apply Fin.ext
              exact Fin.val_cast_of_lt hiii
            have h2 : (ii + 1) % (nn + 2) = ii + 1 := by
              apply Nat.mod_eq_of_lt
              apply Nat.lt_succ_of_lt
              exact hiiii
            have hi5: ii+1 < nn + 2 := by
              linarith
            have h3 : (⟨ii, hiii⟩ : Fin (nn + 2)) + 1 = ⟨ii + 1, hi5⟩ := by
              rw [Fin.add_def]
              exact Fin.mk.inj_iff.mpr h2

            rw [h1, h3]
            apply Eq.symm
            apply Fin.mk.inj_iff.mpr
            exact Eq.symm (Nat.mod_eq_of_lt hii)
    show s.pre.le y x
    let ihht := ihh this

    exact s.pre.le_trans y (s.f x) x ihht slex1


--iteratef_lemma_refのpathを使った証明。
--大小関係があるとiterationで辿り着く。reachを使って書き直すことも可能。
--最初に証明したiteratef_lemma_refの言明。この補題は、path_exists_setupを利用。のちに上のように書き直す。
lemma iteratef_lemma_ref_path (s: Setup α) (x y: s.V) (h: s.pre.le x y):
  ∃ n:Nat, (s.f^[n] x)=y := by
  let pes := path_exists_setup s x y h
  obtain ⟨n, h⟩ := pes
  use n
  obtain ⟨z, hz0,hzn, hz⟩ := h
  have nnf: ∀ nn : Fin (n+1), z nn = s.f^[nn.val] x := by
      let motive : Fin (n+1) → Prop := fun nn => z nn = s.f^[nn.val] x
      apply (@Fin.induction (n) motive)
      case zero =>
        subst hzn hz0
        simp_all only [Fin.natCast_eq_last, Fin.val_zero, Function.iterate_zero, id_eq, motive]
      case succ =>
        intro i hi
        dsimp [motive] at hi
        dsimp [motive]
        rw [←(hz i)]
        rw [hi]
        rw [← hz0]
        --rw [@subtype_val_eq]
        exact Eq.symm (Function.iterate_succ_apply' s.f (↑i) (z 0))
  have h_lt : n < n + 1 := by exact lt_add_one n
  let nnff :=nnf (Fin.mk n h_lt)
  simp at nnff
  rw [←nnff]
  rw [←hzn]
  simp
  congr


--サイズが2以上の同値類は、極大である。
--eqClass_size_ge_two_implies_inverseがpathの議論に依存。
lemma iteratef_size2m (s: Setup α) (x: s.V)  :
  ∀ (n : Nat), 2 ≤ (eqClass_setup s (s.f^[n] x)).card →
  isMaximal s (s.f^[n] x) :=
by
  intro n h
  dsimp [isMaximal]
  exact fun b a => eqClass_size_ge_two_implies_inverse s (s.f^[n] x) h b a

--ノードの上にサイズ2以上が2つあると、それらは一致する。証明の中で極大の定義を使っている。
--でもこれ自体をどこからも参照してない。
lemma iteratef_size2_eq (s: Setup α) (x: s.V)  :
 ∀ (n1 n2 : Nat), 2 ≤ (eqClass_setup s (s.f^[n1] x)).card ∧ 2 ≤ (eqClass_setup s (s.f^[n2] x)).card
  → eqClass_setup s (s.f^[n1] x) = eqClass_setup s (s.f^[n2] x) :=
by
  intro n1 n2 h
  have m1 : isMaximal s (s.f^[n1] x) :=
  by
    exact iteratef_size2m s x n1 h.1
  have m2 : isMaximal s (s.f^[n2] x) :=
  by
    exact iteratef_size2m s x n2 h.2

  by_cases n1 = n2
  case pos =>
    congr
  case neg =>
    have le1: s.pre.le (s.f^[n1] x)  (s.f^[n2] x) :=
    by
      by_cases n1 <= n2
      case pos =>
        --fが大きい方が大きいのは
        have :n1 < n2 :=
        by
          omega
        exact iteratef_lemma_two s x n1 n2 this
      case neg =>
        have : n2 < n1 :=
        by
          simp_all only [not_le]
        have : s.pre.le (s.f^[n2] x)  (s.f^[n1] x) :=
        by
          exact iteratef_lemma_two s x n2 n1 this
        dsimp [isMaximal] at m2
        let m2sf := m2 (s.f^[n1] x)
        exact m2sf this
    have le2: s.pre.le  (s.f^[n2] x)  (s.f^[n1] x) :=
    by
      obtain ⟨val, property⟩ := x
      obtain ⟨left, right⟩ := h
      apply m1
      simp_all only
    exact
      eqClass_eq s (s.f^[n1] x) (s.f^[n2] x)
        (m2 (s.f^[n1] x) (m1 (s.f^[n2] x) (m2 (s.f^[n1] x) (m1 (s.f^[n2] x) le1))))
        (m1 (s.f^[n2] x) (m2 (s.f^[n1] x) (m1 (s.f^[n2] x) (m2 (s.f^[n1] x) le2))))
-/
