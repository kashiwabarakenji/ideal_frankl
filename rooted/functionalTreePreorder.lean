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

--目標補題. function fから作られるpreorderから引き起こされるsetoidの同値類において、同値類の大きさが2以上であれば、極大要素になっているという定理を作りたい。

--Preorderのstar_implies_pathExistsでも同じことを証明している。大きい方から小さい方の鎖になっているような。
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

--fで直前関係になっていれば、a <= bとなること。自明かと思っていたけど、深く定義を追っていかないと証明できなかった。
--size_one_preorder_setup_step も参照。
lemma f_and_pre (su: Setup α) (a b : {x // x ∈ su.V}) (sf : su.f a = b ) : su.pre.le a b := by
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

--補題 頂点aから頂点bにfのパスで辿れるときは、a <= bである。
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

--transitive closureを撮る前の一歩の場合の表現の違いに関する補題。
lemma size_one_preorder_setup_step (s: Setup α) (x y : {x : α // x ∈ s.V}) :
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

--preorderは、rootedset_from_setupの繰り返しで作られている。
lemma size_one_preorder_setup_lemma (s: Setup α) (x y : {x : α // x ∈ s.V}) :
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

--証明できたけど、写像が後ろから前にムカているので逆になっている。外からは使わないけど、次の補題で使っている。
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

--大小関係はfの繰り返しで書けること。こちらよりのちのiteratefのほうがすっきりしているかもしれない。
--setup用になっているのでこれを主に使えば良い。このなかでpath_exists_setup_reverseを使っている。
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
  simp_all
  simp_all only [Fin.coe_eq_castSucc, Fin.val_zero, Nat.cast_zero, zero_add, Fin.val_last, Fin.is_le', Nat.cast_sub,
    Fin.natCast_eq_last, sub_add_cancel, Fin.coe_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, implies_true,
    and_self, z']

--補題。サイズ2以上の同値類は、fの行き先が同値類の外にでない。
lemma eqClass_size_ge_two_implies_outside
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

--補題. サイズが2以上の同値類は、極大要素になること。
--サイズ2以上の同値類からいけるところは、同じ同値類内に必ずなる。このことは前の補題で示されている。
lemma eqClass_size_ge_two_implies_inverse
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α)
    (x : {x // x ∈ s.V})
    (h : 2 ≤ (eqClass_setup s x).card) :
  ∀ y : {x // x ∈ s.V},  s.pre.le x y → s.pre.le y x := by
  intro y h_xy
  obtain ⟨n,z,hz0,hz1,hz⟩ := path_exists_setup s x y h_xy --zはFin n+1で定義されている。

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
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff,
                Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall,
                Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one,
                Subtype.coe_eta, add_lt_add_iff_right, zz', ii]
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
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff,
                Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall,
                Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one,
                Subtype.coe_eta, zz', ii]
            exact this

          · subst hz1 hz0
            simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff,
              pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall, Fin.coe_eq_castSucc,
              Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one, Subtype.coe_eta, zz']
            simp [Fin.val_add]
            apply Fin.ext
            set ii := i.val with hhi
            have hii: ii + 2 < nn + 2 := by
              dsimp [ii]
              simp_all only [Subtype.coe_eta, add_lt_add_iff_right, Fin.is_lt, zz']
            have hiii:ii < nn + 2:= by
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, lt_add_iff_pos_left, add_pos_iff,
                Nat.lt_one_iff, pos_of_gt, or_true, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, Subtype.forall,
                Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Fin.succ_last, Nat.succ_eq_add_one, Fin.succ_zero_eq_one,
                Subtype.coe_eta, zz', ii]
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

-------ここからfの繰り返しに関する部分------

--iterationで辿り着くものには、大小関係がある。
lemma iteratef_lemma (s: Setup α) (x : s.V):
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

--大小関係があるとiterationで辿り着く。
lemma iteratef_lemma_ref (s: Setup α) (x y: s.V) (h: s.pre.le x y):
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

lemma iteratef_lemma_two (s: Setup α) (x: s.V) (n1 n2: Nat) :
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
--証明：鳩の巣原理。
lemma iteratef_pegion (s: Setup α) (x: s.V)  : ∃ (n1 n2: Nat), n1 ≠ n2 ∧ (s.f^[n1] x) = s.f^[n2] x :=
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
lemma iteratef_pegion_ordered (s : Setup α) (x : s.V) :
  ∃ (n1 n2 : ℕ), n1 < n2 ∧ (s.f^[n1] x) = (s.f^[n2] x) := by
  obtain ⟨n1, n2, hne, heq⟩ := iteratef_pegion s x
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
lemma iteratef_size2 (s: Setup α) (x: s.V)  : ∃ (n : Nat), 2 ≤ (eqClass_setup s (s.f^[n] x)).card :=
by
  let h := iteratef_pegion_ordered s x
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

def isMaximal (s: Setup α) (a : s.V) : Prop :=
  ∀ b : s.V, s.pre.le a b → s.pre.le b a

lemma iteratef_size2m (s: Setup α) (x: s.V)  :
  ∀ (n : Nat), 2 ≤ (eqClass_setup s (s.f^[n] x)).card →
  isMaximal s (s.f^[n] x) :=
by
  intro n h
  dsimp [isMaximal]
  exact fun b a => eqClass_size_ge_two_implies_inverse s (s.f^[n] x) h b a

--ノードの上にサイズ2以上が2つあると、それらは一致する。
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

--------------------
----今は使ってないもの。
def finSub (n : ℕ) (i : Fin n) : Fin n :=
  ⟨(n - i.val) - 1, Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.sub_pos_of_lt i.isLt) Nat.zero_lt_one)
      (Nat.sub_le n i.val)⟩

lemma path_exists2 {α : Type} [Fintype α] (R : α → α → Prop) (x y : α)
  (h : Relation.ReflTransGen R x y) :
  ∃ (n : ℕ) (z : Fin (n + 1) → α),
    z 0 = x ∧
    z n = y ∧
    ∀ i : Fin n, R (z i.castSucc) (z i.succ) := by
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
    -- 長さ0のときは i : Fin 0 が存在しないので仮定矛盾 (vacuous truth)
    · intro i
      cases i
      simp_all only [Nat.reduceAdd, Fin.castSucc_mk, Fin.succ_mk, z]
      simp_all only [not_lt_zero']

  case tail b c h₁ h₂ ih =>
    -- 推移的ケース: x から b に到達 (ih)，さらに R b c で b から c
    rcases ih with ⟨n, z, hz₀, hzn, hR⟩
    -- 新しいパスの長さ: n + 1
    use n + 1
    -- i ≤ n のときは z i、そうでなければ c を返すように定義
    use fun i : Fin (n + 2) => if h : (i : ℕ) ≤ n then z ⟨i.val, Nat.lt_succ_of_le h⟩ else c

    -- 1. 始点が x であること
    constructor
    · subst hz₀ hzn
      -- i = 0 のとき i ≤ n は明らかなので z 0 = x
      simp_all only [Fin.natCast_eq_last, Fin.val_zero, zero_le, ← Fin.ext_iff,
                     Fin.zero_eta, ↓reduceDIte]

    -- 2. 終点が c(=y) であること
    constructor
    · simp [Fin.last, hzn]
      intro h

      have : n.succ ≤ n := by
        convert h
        subst hz₀ hzn
        simp_all only [Fin.natCast_eq_last, Nat.succ_eq_add_one]
        simp [Fin.val_add]
      exact False.elim (Nat.not_succ_le_self n this)

    -- 3. 各区間で R が成り立つこと
    · intro i
      simp [Fin.castSucc, Fin.succ]
      split_ifs with h₁ h₂
      · -- i ≤ n かつ (i+1) ≤ n の場合は、IH の hR i を使う
        subst hz₀ hzn
        simp_all only [Fin.natCast_eq_last]
        rename_i h₂_1
        have h₃ := h₂
        simp_all only
        exact hR ⟨i, h₂_1⟩
      · -- i ≤ n だが i+1 ≤ n でない ⇒ i = n の場合
        have : i = Fin.last n := by
          apply Fin.ext
          rw [Fin.val_last]
          subst hz₀ hzn
          simp_all only [not_le, Fin.natCast_eq_last]
          omega
        subst this hz₀ hzn
        simp_all only [Fin.val_last, not_le, Fin.natCast_eq_last]
        -- このときは R (z n) c を使う
        --exact h₂
      · -- i ≤ n だが i+1 ≤ n は偽、かつ else に該当する矛盾ケース
        apply absurd h₁
        subst hz₀ hzn
        simp_all only [not_le, Fin.natCast_eq_last, not_true_eq_false]
        cases i
        simp_all only
        omega
      · -- i ≤ n でない場合も Fin (n+2) の取りうる範囲と矛盾
        apply absurd h₁
        subst hz₀ hzn
        simp_all only [not_le, Fin.natCast_eq_last, not_true_eq_false]
        have := h₁
        simp_all only
        cases i
        simp_all only
        omega

--補題. Subtype上における道の存在定理。後ろにpath_exists_setupがあるので、そちらを主に使うとよい。
lemma path_exists_subtype {α : Type} [Fintype α] (V:Finset α) (R : V → V → Prop) (x y : V) (h : Relation.ReflTransGen R x y) :
  ∃ (n : ℕ) (z : Fin (n + 1) → V), z 0 = x ∧ z n = y ∧ ∀ i : Fin n, R (z i.castSucc) (z i.succ) := by
  -- スカラー版の R を定義：V 上の R を α 上に拡張
  let R' : α → α → Prop := fun a b =>
    if ha : a ∈ V then
      if hb : b ∈ V then R ⟨a, ha⟩ ⟨b, hb⟩
      else false
    else false

  -- x y : V なので、それぞれ α に埋め込める
  let x' : α := x
  let y' : α := y

  -- R' 上での ReflTransGen を構成する
  have h' : Relation.ReflTransGen R' x' y' := by
    -- x = ⟨x.val, x.property⟩, よって R' x y は R x y を含む
    induction h with
    | refl  =>
      apply Relation.ReflTransGen.refl
    | tail a h₁ ih =>
      apply Relation.ReflTransGen.tail ih
      simp_all only [exists_and_left, exists_eq_left, R', x', y']
      simp_all only [Bool.false_eq_true, dite_else_false, coe_mem, ↓reduceDIte, x', y', R']

  -- path_exists を R' に適用
  rcases path_exists R' x' y' h' with ⟨n, z, hz₀, hzn, hR'⟩

  -- z の各点が V にあることを保証しつつ、型を α → V に変換
  have memV : ∀ i : Fin (n + 1), z i ∈ V := by
    -- z 0 = x ∈ V, z n = y ∈ V, 各ステップで R' が成り立つ => 各点 ∈ V
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [hz₀]
      exact x.property
    | succ i ih =>
      specialize ih
      -- R' (z i.castSucc) (z i.succ) により ∃ va vb, ... で z i.succ ∈ V
      simp_all only [Bool.false_eq_true, dite_else_false, Fin.natCast_eq_last, x', R', y']
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      subst hz₀ hzn
      simp_all only [R']
      cases hR' i
      simp_all only [R']
      rename_i h_1
      obtain ⟨w_1, h_1⟩ := h_1
      simp_all only [R']

  -- z を V 型に変換
  let z' : Fin (n + 1) → V := fun i => ⟨z i, memV i⟩

  -- パス条件の検証
  use n, z'
  constructor
  · -- z' 0 = x
    apply Subtype.ext
    exact hz₀
  constructor
  · -- z' n = y
    apply Subtype.ext
    exact hzn
  · -- 各ステップで R が成り立つ
    intro i
    specialize hR' i
    simp_all only [Bool.false_eq_true, dite_else_false, Fin.natCast_eq_last, exists_true_left, x', y', R', z']

--reverseだけでよくないか。
/-
lemma path_exists {α : Type} [Fintype α] (R : α → α → Prop) (x y : α)
  (h : Relation.ReflTransGen R y x) :
  ∃ (n : ℕ) (z : Fin (n + 1) → α),
    z 0 = x ∧
    z n = y ∧
    ∀ i : Fin n, R (z i.castSucc) (z i.succ):= by
  --let R' : α → α → Prop := fun x y => R y x
  /-have :Relation.ReflTransGen R' x y := by
    induction h
    case refl x =>
      apply Relation.ReflTransGen.refl
    case tail a b h₁ h₂ ih =>
      simp_all only [Function.const_apply, R']
      exact Relation.ReflTransGen.head h₂ ih
  -/ --R'の順番を変える必要はなかった。
  obtain ⟨n, z, hz₀, hzn, hR⟩ := path_exists_reverse R y x h
  by_cases hn:n = 0
  case pos =>
    use n
    rw [hn]
    subst hn hz₀ hzn
    simp_all only [IsEmpty.forall_iff, Fin.isValue, Nat.reduceAdd, Nat.cast_zero, and_true, and_self,
      exists_apply_eq_apply]
  case neg =>

    let z' : Fin (n + 1) → α := fun i => z (n - i)
    use n
    use z'
    constructor
    · dsimp [z']
      subst hz₀ hzn
      simp_all only [Fin.natCast_eq_last, Fin.val_zero, zero_le, Fin.zero_eta]
      simp_all only [sub_zero, z']

    · constructor
      · dsimp [z']
        subst hz₀ hzn
        simp_all only [Fin.natCast_eq_last, sub_self, z']
      · intro i
        specialize hR (finSub n i)
        dsimp [z']
        dsimp [finSub] at hR
        --simp_all only [Fin.castSucc, Fin.succ]
        --hRは、fin nなのかfin n+1なのか。00この上まではFin nっぽい。castSuccの影響でn+1になっている。

        have t1: z (n - ↑i - 1 + 1) = z (↑n - i.castSucc) := by
          subst hz₀ hzn
          simp_all only [Fin.natCast_eq_last, Fin.coe_eq_castSucc, sub_add_cancel, z']
        have t2: z (n - ↑i - 1) =  z (↑n - i.succ) := by
          subst hz₀ hzn
          simp_all only [Fin.natCast_eq_last, Fin.coe_eq_castSucc, sub_add_cancel, z']
          sorry
        rw [←t2]
        rw [←t1]
        sorry        --hRとRは逆の関係になっている。
-/
