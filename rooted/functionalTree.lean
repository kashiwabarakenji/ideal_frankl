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
import rooted.functionalPreorder

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

--補題1. function fから作られるpreorderから引き起こされるsetoidの同値類において、同値類の大きさが2以上であれば、極大要素になっているという定理を作りたい。
--補題2. functionalなpreorderから引き起こされるsetoidの同値類のpartial orderに関して、直前の要素はたかだか一つである。
--instance size_one_circuits_preorder  {α : Type} [Fintype α]  [DecidableEq α] (RS : RootedSets α) -- [DecidablePred (rootedsetToClosureSystem RS).sets] : Preorder {x // x ∈ RS.ground} where
--noncomputable instance size_one_preorder {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty):
-- Preorder { x // x ∈ V } := size_one_circuits_preorder (rootedset_onestem_eachvertex_V V f valid nonemp)
--を利用して、functionからPreorderを作成。
--instance setoid_preorder {α : Type}[Preorder α]: Setoid α := ⟨@equiv_rel α _, equiv_rel_equiv⟩
--そのPreorderから
--instance quotient_partial_order {α : Type}[Preorder α]: PartialOrder (Quotient (@setoid_preorder α _)) where
--を利用して、半順序を作る。
structure Setup (α : Type) [Fintype α] [DecidableEq α] where
  (V        : Finset α)
  (nonemp   : V.Nonempty)
  (f        : V → V)
  (valid    : ∀ v : V, f v ≠ v)
  (pre      : Preorder {x // x ∈ V})
  (setoid   : Setoid {x // x ∈ V})
  (h_pre    : pre = size_one_preorder V f valid nonemp)
  (h_setoid : setoid = setoid_preorder)
  (po       : PartialOrder (Quotient setoid))

--setupからrootedsetを作るもの。fから作るには、rootedset_onestem_eachvertex_Vを利用すれば良い。setupに含めてもよいかも。
--RootedSetsから2項関係にするには、R_from_RS1 を用いると、ステムサイズ1のものだけから2項関係を作ってくれる。
noncomputable def rootedset_from_setup {α : Type} [Fintype α] [DecidableEq α] (s: Setup α) : RootedSets α :=
 rootedset_onestem_eachvertex_V s.V s.f s.valid s.nonemp

def isMaximal [Preorder α] (a : α) : Prop :=
  ∀ b : α, a ≤ b → b ≤ a

/--
商集合上 `(Quotient setoid_preorder, ≤)` における「極大元」であることを表す述語です。
-/
def isMaximalQ [Preorder α](x : Quotient (@setoid_preorder α _)) : Prop :=
  ∀ y, x ≤ y → y ≤ x

noncomputable def eqClass_subtype {α : Type} [DecidableEq α] (V : Finset α) [Setoid {x : α // x ∈ V}] (x : {x : α // x ∈ V}) : Finset {x // x ∈ V} :=
  V.attach.filter (fun y => Setoid.r x y)

noncomputable def eqClass_setup {α : Type} [DecidableEq α][Fintype α] (s: Setup α) (x : {x : α // x ∈ s.V}) : Finset {x // x ∈ s.V} :=
  s.V.attach.filter (fun y => s.setoid.r x y)

--同じ同値類に入っている要素には大小関係がある。
lemma eqClass_le (s: Setup α) : (x y: {x : α // x ∈ s.V}) → y ∈ eqClass_setup s x → s.pre.le x y :=
by
  intro x y h
  simp [eqClass_setup] at h
  rw [s.h_setoid] at h
  simp_all only [AntisymmRel.setoid_r]
  obtain ⟨val, property⟩ := x
  obtain ⟨val_1, property_1⟩ := y
  exact h.1

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
    · --have : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := rfl
      --simp [this, hzn]  -- z (n + 1) = c を示す（ただし c = y）
      --simp only [Fin.last]
      have : ↑(Fin.last (n + 1)) = n + 1 := rfl
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

def finSub (n : ℕ) (i : Fin n) : Fin n :=
  ⟨(n - i.val) - 1, Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.sub_pos_of_lt i.isLt) Nat.zero_lt_one)
      (Nat.sub_le n i.val)⟩

--そもそもこの命題は必要で、成り立つのか？reverseだけでよくないか。
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

--補題. Subtype上における道の存在定理
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


--fで直前関係になっていれば、a <= bとなること。自明かと思っていたけど、深く定義を追っていかないと証明できなかった。
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

--s.preのほうはsize_one_preorderやsize_one_circuits_preorderでRootedSetsを定義して、そこからpreorder.R_hatを使って集合族でPreorderを定義。
--右辺のほうは単純にtransitive closureで定義。
--lemma ReflTransGen.to_R_hat {R : α → α → Prop} {x y : α} (h : Relation.ReflTransGen R x y) : R_hat R x y := by
--lemma R_hat.to_ReflTransGen {R : α → α → Prop} {x y : α} (h : R_hat R x y) : Relation.ReflTransGen R x y
--の2つの補題を使うといいかも。
lemma size_one_preorder_setup_lemma (s: Setup α) (x y : {x : α // x ∈ s.V}) :
  s.pre.le x y ↔  @Relation.ReflTransGen s.V (R_from_RS1 (rootedset_from_setup s))  y x:=
by
  --dsimp [LE.le]
  --dsimp [s.h_pre]
  simp [rootedset_from_setup]
  rw [s.h_pre]
  dsimp [size_one_preorder]
  dsimp [size_one_circuits_preorder]
  --dsimp [preorder.R_hat]
  --dsimp [preorder.S_R]
  dsimp [rootedset_onestem_eachvertex_V]
  apply Iff.intro
  · intro h
    apply preorder.R_hat.to_ReflTransGen
    exact h

  · intro h
    intro s1 hs1
    exact preorder.ReflTransGen.to_R_hat h s1 hs1

--証明できたけど、写像が後ろから前にムカているので逆になっている。(z i.castSucc) = s.f (z i.succ)がまずおかしい。
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

lemma path_exists_setup (s: Setup α) (x y : {x : α // x ∈ s.V}) :
  s.pre.le x y →
  ∃ (n : ℕ) (z : Fin (n + 1) → {x : α // x ∈ s.V}), z 0 = x ∧ z n = y ∧ ∀ i : Fin n, s.f (z i.castSucc) = (z i.succ) :=
by
  intro h
  let R := R_from_RS1 (rootedset_from_setup s)
  have h' : @Relation.ReflTransGen s.V R y x := by
    exact (size_one_preorder_setup_lemma s x y).mp h

  dsimp [R] at h'
  let pe := path_exists (R_from_RS1 (rootedset_from_setup s)) y x h'
  obtain ⟨n, z, hz₀, hzn, hstep⟩ := pe
  let z' : Fin (n + 1) → s.V := fun i => z (n - i)
  use n
  use z'
  constructor
  ·
    subst hz₀ hzn
    simp_all only [Fin.natCast_eq_last, sub_zero, R, z']
  constructor
  ·
    subst hz₀ hzn
    simp_all only [Fin.natCast_eq_last, sub_self, z', R]
  · intro i
    specialize hstep i
    let sop := size_one_preorder_setup_step s (z' i.castSucc) (z' i.succ)
    rw [←sop]
    dsimp [R_from_RS1]
    dsimp [rootedset_from_setup]
    dsimp [rootedset_onestem_eachvertex_V]
    subst hzn hz₀
    simp_all only [Fin.natCast_eq_last, R]
    have : (z' i.castSucc) ∉ ({z' i.succ}:Finset s.V) := by
      intro h
      rw [Finset.mem_singleton] at h
      dsimp [z'] at h
      search_proof

    let vp := ValidPair.mk {z' i.succ} (z' i.castSucc) (by sorry)
    simp
    constructor
    ·
      constructor
      · use (z i.castSucc)
        have : ↑(z i.castSucc) ∈ s.V:= by
          simp_all only [coe_mem, z', R]
        use this
        simp

        sorry
      · sorry
    · sorry



lemma path_exists_setup2 (s: Setup α) (x y : {x : α // x ∈ s.V}) :
  s.pre.le y x →
  ∃ (n : ℕ) (z : Fin (n + 1) → {x : α // x ∈ s.V}), z 0 = x ∧ z n = y ∧ ∀ i : Fin n, s.f (z i.castSucc) = (z i.succ) :=
by
  intro h
  let R := R_from_RS1 (rootedset_from_setup s)
  have h' : @Relation.ReflTransGen s.V R x y := by
    exact (size_one_preorder_setup_lemma s y x).mp h
  dsimp [R] at h'
  let pe := path_exists (R_from_RS1 (rootedset_from_setup s)) x y h'
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


















    --いままでのなにかの定理を使えば証明できる。それを補題として独立させる必要がある。
    --すなわち、R_from_RS1 (rootedset_from_setup s)のR_hatで定義した順序と、s.pre.le=size_one_preorderの順序が一致することを示す。


--補題。上の補題は、途中のノードに対しても成り立つこと。
lemma path_implies_front {α : Type} [Fintype α] [DecidableEq α] (s : Setup α) (a b : {x // x ∈ s.V})
  (n : ℕ) (z : Fin (n + 1) → {x // x ∈ s.V})
  (h0 : z 0 = a) (hn : z n = b)
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
      subst hn h0
      omega
    let i' : Fin (n) := ⟨i.val, np1⟩
    have h_i' : z i'.castSucc = z' i.castSucc := by
      simp [z', Fin.castSucc]
      subst hn h0
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
      subst hn h0
      simp_all only [Fin.castSucc_mk, Fin.coe_castSucc, z', i']
      ext : 1
      congr
      simp_all only [Nat.add_mod_mod, Nat.mod_add_mod, z', i']
      rw [Nat.mod_eq_of_lt (Nat.succ_le_succ np1)]
    subst hn h0
    simp_all only [Fin.castSucc_mk, Fin.coe_castSucc, Fin.succ_mk, Fin.val_succ, Nat.cast_add, Nat.cast_one, z', i']
    specialize h i'
    simp_all only [Fin.castSucc_mk, Fin.succ_mk, z', i']
  subst hn h0
  simp_all only [Fin.coe_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, z']
  use z'
  simp_all only [Fin.val_zero, Nat.cast_zero, Fin.val_last, Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.val_succ,
    Nat.cast_add, Nat.cast_one, implies_true, and_self, z']


lemma path_implies_rear {α : Type} [Fintype α] [DecidableEq α] (s : Setup α) (a b : {x // x ∈ s.V})
  (n : ℕ) (z : Fin (n + 1) → {x // x ∈ s.V})
  (h0 : z 0 = a) (hn : z n = b)
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
      subst hn h0
      omega
    let i' : Fin (n) := ⟨i.val + ii.val, np1⟩
    have h_i' : z i'.castSucc = z' i.castSucc := by
      simp [z', Fin.castSucc]
      subst hn h0
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
      subst hn h0
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
    subst hn h0
    simp_all only [Fin.castSucc_mk, Fin.coe_castSucc, Fin.succ_mk, Fin.val_succ, Nat.cast_add, Nat.cast_one, z', i']
    specialize h i'
    simp_all only [Fin.castSucc_mk, Fin.succ_mk, z', i']
  subst hn h0
  simp_all only [Fin.coe_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, Fin.natCast_eq_last, z']
  use z'
  simp_all
  simp_all only [Fin.coe_eq_castSucc, Fin.val_zero, Nat.cast_zero, zero_add, Fin.val_last, Fin.is_le', Nat.cast_sub,
    Fin.natCast_eq_last, sub_add_cancel, Fin.coe_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, implies_true,
    and_self, z']

--補題. 同じ同値類の異なる頂点間の道は、同値類の外を通らないこと。
--証明。同じ同値類の頂点をaとbとする。上の補題より、aからbへのパスがある。aのとなりの頂点をvとすると、a <= vで、v <= bなので、

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
    --dsimp [eqClass_setup] at hz
    apply eqClass_le
    simp_all only [ne_eq, sdiff_eq_empty_iff_subset, Finset.subset_singleton_iff, not_or, mem_sdiff,
      Finset.mem_singleton, eqy]

  #check path_exists2 s.pre.le y z


  let a := x.attach.filter (fun z => s.f z = y)
  let b := x.attach.filter (fun z => s.f z ≠ y)
  have h1 : x.attach = a ∪ b := by
    apply Finset.ext
    intro z
    simp [Finset.mem_union, Finset.mem_filter]
    split
    · intro hz
      by_cases hz_f : s.f z = y
      · left
        simp [hz_f]
      · right
        simp [hz_f]
    · intro hz
      cases hz
      · simp [hz]
      · simp [hz]
  have h2 : a.card = 1 := by
    rw [←Finset.card_attach]
    rw [h1]
    have h2_1 : a ∩ b = ∅ := by
      apply Finset.eq_empty_of_forall_not_mem
      intro z hz
      simp [Finset.mem_inter] at hz
      cases hz
      have hz_f : s.f z = y := by
        simp [Finset.mem_filter] at hz_left
        exact hz_left
      have hz_f' : s.f z ≠ y := by
        simp [Finset.mem_filter] at hz_right
        exact hz_right
      contradiction
    rw [Finset.card_disjoint_union h2_1]
    simp
  have h3 : b.card = x.card - 1 := by
    rw [←Finset.card_attach]
    rw [h1]
    have h3_1 : a ∩ b = ∅ := by
      apply Finset.eq_empty_of_forall_not_mem
      intro z hz
      simp [Finset.mem_inter] at hz
      cases hz
      have hz_f : s.f z = y := by
        simp [Finset.mem_filter] at hz_left
        exact hz_left
      have hz_f' : s.f z ≠ y := by
        simp [Finset.mem_filter] at hz_right
        exact hz_right
      contradiction
    rw [Finset.card_disjoint_union h3_1]
    simp
  have h4 : 2 ≤ x

--補題. サイズが2以上の同値類は、極大要素になること。
lemma eqClass_size_ge_two_implies_inverse
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α)
    (x : {x // x ∈ s.V})
    (h : 2 ≤ (eqClass_setup s x).card) :
  ∃ y : {x // x ∈ s.V}, y ≠ x ∧ s.pre.le y x ∧ s.f y = x := by
    sorry
/-
   --同じ同値類の要素が2つ以上あるとき、それらの頂点の関数の行き先は、同じ同値類になる。

--Quotientとどう違う。
noncomputable def eqClass {α : Type}  [DecidableEq α] [Setoid α] (V : Finset α) (x : α) : Finset α :=
  V.filter (fun y => Setoid.r x y)

theorem eqClass_card_ge_two_implies_maximal_nonsubtype
    {α : Type} [Fintype α] [DecidableEq α]
    (V : Finset α) (f : V → V)--言明には必要ない。
    (valid : ∀ v : V, f v ≠ v) (nonemp : V.Nonempty)--言明には必要ない。
    [Preorder {x // x ∈ V}] --これは言明に必要。
    [Setoid α]--[Setoid {x // x ∈ V}] 言明に必要。後ろの方だとうまくいかない。
    --(h_pre : Preorder {x // x ∈ V} = size_one_preorder V f valid nonemp)
    --(h_setoid : Setoid {x // x ∈ V} )--= setoid_preorder)
    --(s: Setup α)
    (x : {x // x ∈ V})
    (h : 2 ≤ (eqClass V x.1).card)
  : ∀ y : {x // x ∈ V}, x ≤ y → y ≤ x := by
  intro y h_xy
  let RS := rootedset_onestem_eachvertex_V V f valid nonemp
  let R := R_from_RS1 RS
  --rw [h_pre, size_one_preorder, size_one_circuits_preorder] at h_xy ⊢

  --dsimp [size_one_preorder] at h_xy ⊢
  --simp only [preorder.R_hat] at h_xy ⊢
  -- 同値類は x とその逆像
  have h_eq_class : eqClass V x.val = Finset.image (λ v => v) {v | f v = x.val} ∪ {x.val} := by
    apply Finset.ext
    intro z
    simp [Quotient.mk, Setoid.r, h_setoid, equiv_rel]
    constructor
    · intro ⟨h_z_x, h_x_z⟩
      by_cases h_z_x_eq : z = x
      · simp [h_z_x_eq]
      · have h_R_z_x : R z x := by
          exists ⟨{z.val}, x.val, by simp [valid]; intro h; subst h; apply valid x.val; simp⟩
          simp [RS, rootedset_onestem_eachvertex_V]
          refine ⟨?_, rfl, rfl⟩
          apply Finset.mem_image_of_mem (λ v => ValidPair.mk {f v.val} v (by simp [valid]))
          simp [Finset.attach]
          exact x.property
        simp [R, R_from_RS1, RS, rootedset_onestem_eachvertex_V] at h_R_z_x
        simp [h_R_z_x]
    · intro h_z_in
      simp at h_z_in
      cases h_z_in <;> [subst h_z_in; simp]
      · exact ⟨le_refl x, le_refl x⟩
      · intro s hs_s h_x_s
        simp [S_R, closedUnder] at hs_s
        have h_R_z_x : R z x := by
          exists ⟨{z.val}, x.val, by simp [valid]; intro h; subst h; apply valid x.val; simp⟩
          simp [RS, rootedset_onestem_eachvertex_V]
          refine ⟨?_, rfl, rfl⟩
          apply Finset.mem_image_of_mem (λ v => ValidPair.mk {f v.val} v (by simp [valid]))
          simp [Finset.attach]
          exact x.property
        exact hs_s h_R_z_x h_x_s
      · exact ⟨by simp, by simp⟩
  -- y は同値類内
  have h_y_in : y ∈ Quotient.mk (Setoid.r) x := by
    simp [Quotient.mk, Setoid.r, h_setoid, equiv_rel]
    exact ⟨h_xy, h_xy⟩
  rw [h_eq_class] at h_y_in
  simp at h_y_in
  cases h_y_in
  · subst h_y_in
    exact le_refl x
  · intro s hs_s h_x_s
    simp [S_R, closedUnder] at hs_s
    have h_R_y_x : R y x := by
      exists ⟨{y.val}, x.val, by simp [valid]; intro h; subst h; apply valid x.val; simp⟩
      simp [RS, rootedset_onestem_eachvertex_V]
      refine ⟨?_, rfl, rfl⟩
      apply Finset.mem_image_of_mem (λ v => ValidPair.mk {f v.val} v (by simp [valid]))
      simp [Finset.attach]
      exact x.property
    exact hs_s h_R_y_x h_x_s
-/
/-
theorem eqClass_card_ge_two_implies_maximal
    {α : Type} [Fintype α] [DecidableEq α] [Setoid α]
    (V : Finset α) (f : V → V)
    (valid : ∀ v : V, f v ≠ v)
    (nonemp : V.Nonempty)
    [inst : Preorder {x // x ∈ V}]  -- size_one_preorder などを想定
    (x : {x // x ∈ V})
    (h : 2 ≤ (eqClass V x.1).card)
  : ∀ y, x ≤ y → y ≤ x := by
-/


/-
「元の前順序で `a` が極大元である」ことと、
「商集合上で `Quotient.mk a` が極大元である」ことは同値である、という主張を証明します。
-/

omit [Fintype α] in
omit [DecidableEq α] in
lemma isMaximal_iff [Preorder α] (a : α) :
  isMaximal a ↔ isMaximalQ (Quotient.mk setoid_preorder a) := by
  constructor
  · --------------------
    -- (→) 方向の証明
    intro ha  -- `ha` : a は元の前順序で極大
    intro x hx
    -- x は商集合上の元なので、代表元 b を取り出す
    rcases Quotient.exists_rep x with ⟨b, rfl⟩
    -- hx : Quotient.mk a ≤ Quotient.mk b から a ≤ b を得る
    rw [quotient_le_iff] at hx
    -- a が極大なので b ≤ a になる
    have hba := ha b hx
    -- すると商集合上も Quotient.mk b ≤ Quotient.mk a が成り立つ
    rw [quotient_le_iff]
    exact hba
  · --------------------
    -- (←) 方向の証明
    intro ha  -- `ha` : 商集合で Quotient.mk a が極大
    intro b hab
    -- a ≤ b から商集合でも Quotient.mk a ≤ Quotient.mk b となる
    have h : (Quotient.mk setoid_preorder a : Quotient setoid_preorder) ≤ Quotient.mk setoid_preorder b := by
      rw [quotient_le_iff]
      exact hab
    -- 商集合での極大性から Quotient.mk b ≤ Quotient.mk a
    specialize ha (Quotient.mk setoid_preorder b) h
    -- これを a, b 間の関係に戻す
    rw [quotient_le_iff] at ha
    exact ha

/--
「元の前順序での極大元の集合」-
「商集合上での極大元の集合」とが、商写像 `Quotient.mk` を通じて
ちょうど同じものになる、ということを集合レベルでも示せます。
-/
noncomputable def MaxSet  [Preorder α][Fintype α]:= ({ a : α | isMaximal a }:Finset α)
noncomputable def MaxQuotSet {α : Type} [Preorder α] [Fintype α] : Finset (Quotient (@setoid_preorder α _)) :=
  { x : Quotient (@setoid_preorder α _) | isMaximalQ x }

omit [Fintype α] [DecidableEq α] in
lemma MaxQuotSet_eq_image [Preorder α] [Fintype α]:
  MaxQuotSet = Finset.image (Quotient.mk (@setoid_preorder α _)) MaxSet := by
  ext x
  constructor
  · --------------------
    -- (→) x が商集合で極大ならば、その代表元 a も元の前順序で極大
    intro hx
    rcases Quotient.exists_rep x with ⟨a, rfl⟩
    rw [Finset.mem_image]
    use a
    constructor
    · -- a が元の前順序で極大であることは、isMaximal_iff の逆向きで分かる
      dsimp [MaxQuotSet] at hx
      rw [Finset.mem_filter] at hx
      dsimp [MaxSet]
      rw [mem_filter]
      simp_all only [Finset.mem_univ, true_and]
      rw [isMaximal_iff]
      simp_all only
    · rfl  -- x = Quotient.mk a
  · --------------------
    -- (←) x が Quotient.mk a で、a が元の前順序で極大なら、x も商集合上で極大
    intro hx
    dsimp [MaxQuotSet]
    rw [Finset.mem_image] at hx
    rw [Finset.mem_filter]
    constructor
    · simp_all only [Finset.mem_univ]
    · dsimp [isMaximalQ]
      intro y hy
      rcases Quotient.exists_rep y with ⟨b, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hx
      dsimp [MaxSet] at ha
      rw [Finset.mem_filter] at ha
      simp_all only [Finset.mem_univ, true_and]
      apply ha
      exact hy
