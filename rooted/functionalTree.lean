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
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne
import rooted.functionalCommon
import rooted.functionalPreorder

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]
/-
instance subtype_setoid (V : Finset α) [Setoid α] : Setoid { x : α // x ∈ V } :=
{ r := λ a b =>
   Setoid.r a.val b.val
  iseqv :=
  {
    λ a => by
    λ a b => Setoid.r_symm
    λ a b c => Setoid.r_trans
  }

 }
 -/

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
/-
  case tail _ z yz ih =>
    -- 既に x から z へのパスがあると仮定 (ih) し，そこへ y を足せばよい
    rcases ih with ⟨n, w, w0, wn, hw⟩
    exists n.succ
    -- パスを一つ伸ばす: 最後だけ y に差し替えた列を作る
    let w' : Fin (n.succ + 1) → α := fun i =>
      if h : i.val < n.succ then w ⟨i.val, h⟩ else y
    exists w'
    constructor
    · -- z 0 = x を保つ
      have : (0 : Fin (n.succ+1)).val < n.succ := Nat.zero_lt_succ n
      simp [w', this, w0]
    constructor
    · -- z n.succ = y となる
      rename_i c
      have : ¬ (n.succ : Fin (n.succ+1)).val < n.succ := by
        refine Nat.not_lt.mpr ?_
        simp
        norm_cast
        sorry

      simp [w', this, wn]
      sorry
    · -- 各区間で R が成り立つことを示す
      intro i
      have : i.val < n.succ := by
        apply Nat.lt_succ_of_lt --i.isLt
        sorry
      simp [w', this]
      -- ここで次の要素 i.succ は n.succ 未満なら w で与えられ，
      -- n.succ ちょうどなら y なので，z → y の元の仮定 yz を用いる
      by_cases c : i.succ.val < n.succ
      · sorry
        --simp [w', c]
        --exact hw i
      · -- i.succ = n.succ の場合
        have eq : i.succ.val = n.succ := by
          exact Nat.le_antisymm (Nat.le_of_lt_succ i.succ.isLt) (Nat.le_of_not_lt c)
        split
        · -- i.succ = n.succ なので yz を使う
          subst w0 wn
          simp_all only [Nat.succ_eq_add_one, Fin.is_lt, Fin.val_succ, add_lt_add_iff_right, not_true_eq_false, w']
        · sorry
-/


lemma path_from_le {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α)
    (x y : {x // x ∈ s.V})
    (h_le : s.pre.le x y) :
  ∃ (n : ℕ) (z : Fin (n + 1) → {x // x ∈ s.V}), z 0 = x ∧ z n = y ∧ ∀ i : Fin n, s.f (z i) = z (Fin.succ i) := by



lemma eqClass_size_ge_two_implies_inverse
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α)
    (x : {x // x ∈ s.V})
    (h : 2 ≤ (eqClass_setup s x).card) :
  ∃ y : {x // x ∈ s.V}, y ≠ x ∧ s.pre.le y x ∧ s.f y = x := by
  let RS := rootedset_onestem_eachvertex_V s.V s.f s.valid s.nonemp
  let R := R_from_RS1 RS

  rw [s.h_setoid] at h
  simp [eqClass_subtype, Setoid.r, setoid_preorder, equiv_rel] at h
  have h_nontriv : ∃ y, y ≠ x ∧ y ∈ Finset.univ.filter (λ y => x ≤ y ∧ y ≤ x) := by
    apply Finset.card_ge_two_implies_exists_distinct
    exact h
  rcases h_nontriv with ⟨y, h_y_ne_x, h_y_in⟩
  simp [Finset.mem_filter, Finset.mem_univ, true_and] at h_y_in
  exists y
  refine ⟨h_y_ne_x, h_y_in.2, ?_⟩
  rw [s.h_pre] at h_y_in
  simp only [size_one_preorder, size_one_circuits_preorder, preorder.R_hat] at h_y_in
  have h_R_y_x : R y x := by
    exists ⟨{y.val}, x.val, by simp [s.valid]; intro h; subst h; apply s.valid x.val; simp⟩
    simp [RS, rootedset_onestem_eachvertex_V]
    refine ⟨?_, rfl, rfl⟩
    apply Finset.mem_image_of_mem (λ v => ValidPair.mk {s.f v.val} v (by simp [s.valid]))
    simp [Finset.attach]
    exact x.property
  simp [R, R_from_RS1, RS, rootedset_onestem_eachvertex_V] at h_R_y_x
  exact h_R_y_x






   --もうちょっと補題を作った方がいいかも。
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
