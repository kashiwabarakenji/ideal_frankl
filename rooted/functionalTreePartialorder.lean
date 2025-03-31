import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne
import rooted.functionalCommon
import rooted.functionalTreePreorder


open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]
--ここまでで、サイズが2以上の同値類は、極大なものしかないことを証明した。
--任意のノードの上には、極大なノードの同値類がちょうど1つ存在することを示すことになる。
--辿り着ける極大な同値類が2つもってくると、必ず一致することを示す必要がある。
--2つの頂点に辿り着くまでのパスが同じことを示すのがよいか。これも帰納法か。
--補題。あるノードから2つの頂点にたどり着いたときに、その頂点の近い方までの道は一致する。
--補題。あるノードから歩数が決まれば、道が確定し、頂点が決定する。
--その道上以外にそのノードよりも上のものは存在しないし、上のものはかならず道上にある。

  --ここからは半順序に関するもの。

  --preorderの大きさ2以上の同値類は、半順序の極大要素になる。
  --preorderの極大要素は、同値類の極大要素になる。これは示し済み。
  --半順序で大小関係があったら、それをpullbachした前順序でも大小関係がある。示し済み。
  --前順序で大小関係があったら、それをpushforwardした半順序でも大小関係がある。示し済み。

--前順序の要素を対応する同値類に移す。setoid preorderのキメ打ちなので、setup系ではない。
--setupに対して、pullbackを定義した方が良い。
--noncomputable def pullback {α : Type} [Fintype α] [Preorder α]
--  (J : Finset (Quotient (@setoid_preorder α _))) : Finset α :=
--  { a : α | Quotient.mk setoid_preorder a ∈ J }
--noncomputable def pushforward {α : Type} [Fintype α] [Preorder α]
--  (I : Finset α) : Finset (Quotient (@setoid_preorder α _)) :=
--  Finset.univ.filter (fun q => ∃ a ∈ I, Quotient.mk setoid_preorder a = q)
--lemma quotient_le_iff {α : Type}[Preorder α] (a b : α) :
--  (quotient_partial_order.le (Quotient.mk setoid_preorder a : Quotient (@setoid_preorder α _))  (Quotient.mk setoid_preorder b)) ↔ a ≤ b := by

--quotient_partial_orderよりも証明が長いのは、preorderが間接的に定義されているから？
def partialOrder_from_preorder (s : Setup α) : PartialOrder (Quotient s.setoid) where
  le := by
    exact Quotient.lift₂ (fun x y => s.pre.le x y)
      (by

        intros a₁ b₁ a₂ b₂ h₁ h₂

        -- まず setoid の定義を展開
        have h₁' := s.h_setoid ▸ h₁
        have h₂' := s.h_setoid ▸ h₂

        simp [setoid_preorder] at h₁' h₂'

        rcases h₁' with ⟨h₁_le, h₁_ge⟩
        rcases h₂' with ⟨h₂_le, h₂_ge⟩

        apply propext
        constructor
        · intro h
          exact le_implies_le_of_le_of_le h₁_ge h₂_le h
        · intro h
          exact le_implies_le_of_le_of_le h₁_le h₂_ge h

      )
  le_refl := by
    intro xx
    simp_all only
    simp [Quotient.lift₂]
    induction xx using Quotient.inductionOn
    simp_all only [Quotient.lift_mk, le_refl]

  le_trans := by
    intro x y z
    simp_all only
    induction x using Quotient.inductionOn
    simp_all only [Quotient.lift_mk, Quotient.lift₂]
    induction y using Quotient.inductionOn
    induction z using Quotient.inductionOn
    simp_all only [Quotient.lift_mk, Quotient.lift₂]
    rename_i a a_1 a_2
    intro a_3 a_4
    exact a_3.trans a_4

  le_antisymm := by
    intro x y
    simp_all only
    induction x using Quotient.inductionOn
    rename_i a
    intro a_1 a_2
    simp_all only [Quotient.lift_mk]
    symm
    induction' y using Quotient.inductionOn with y
    simp_all only [Quotient.lift_mk, Quotient.eq]
    induction s
    rename_i h_pre setoid h_setoid
    subst h_pre h_setoid
    simp_all only [AntisymmRel.setoid_r]
    trivial

noncomputable def spullback  (s: Setup α) (J : Finset (Quotient s.setoid)) : Finset s.V :=
  { a : s.V | Quotient.mk s.setoid a ∈ J }

noncomputable def spushforward  (s: Setup α) (I : Finset s.V) : Finset (Quotient s.setoid) :=
  Finset.univ.filter (fun q => ∃ a ∈ I, Quotient.mk s.setoid a = q)

--半順序を加えたSetup
--上のinstanceは、s.po.leとは別物になってしまうので、instanceでなくてdefのほうがよい。
structure Setup2 (α : Type) [Fintype α] [DecidableEq α] extends Setup α where
  (po       : PartialOrder (Quotient setoid))
  (h_po     :  po = partialOrder_from_preorder toSetup)

--前に定義していたquotient_partial_orderと内容的に被っている。
instance (s : Setup2 α) : PartialOrder (Quotient s.setoid) := s.po



def isMaximal (s: Setup2 α) (a : s.V) : Prop :=
  ∀ b : s.V, s.pre.le a b → s.pre.le b a

--instを入れなくても、自動的にs.poのインスタンスを使ってくれている。
lemma pullback_preorder_lemma (s : Setup2 α)-- [inst : PartialOrder (Quotient s.setoid)]
 (j1 j2 : (Quotient s.setoid)) (x1 x2 : s.V) :
  Quotient.mk s.setoid x1 = j1 → Quotient.mk s.setoid x2 = j2 → s.po.le j1 j2 → s.pre.le x1 x2 :=
by
  intro h1 h2 h3
  rw [@Setup2.h_po] at h3
  dsimp [partialOrder_from_preorder] at h3
  simp [LE.le, partialOrder_from_preorder, Quotient.lift₂] at h3
  subst h2 h1
  simp_all only [Quotient.lift_mk]

lemma pushforward_preorder_lemma (s : Setup2 α) (x1 x2 : s.V) :
  s.pre.le x1 x2 → s.po.le (Quotient.mk s.setoid x1)  (Quotient.mk s.setoid x2) :=
by
  intro h
  rw [@Setup2.h_po]
  dsimp [partialOrder_from_preorder]
  simp_all only

/--
商集合上 `(Quotient setoid_preorder, ≤)` における「極大元」であることを表す述語です。
-/
--この順序はPartial orderの順序。まだ使ってないかも。setupで書き直す。
def isMaximalQ (s : Setup2 α) (x : Quotient (s.setoid)) : Prop :=
  ∀ y, s.po.le x y → s.po.le y x

--lemma eqClass_size_ge_two_implies_inverse
--    {α : Type} [Fintype α] [DecidableEq α]
--    (s : Setup α)
--    (x : {x // x ∈ s.V})
--    (h : 2 ≤ (eqClass_setup s x).card) :
--  ∀ y : {x // x ∈ s.V},  s.pre.le x y → s.pre.le y x := by
-- で大きさ2以上の同値類は、極大になることをいっているが、極大性自体は定義していない。

--isMaximalの定義もsetupに合わせる必要があるのでは。
lemma isMaximal_iff (s: Setup2 α) (a : s.V) :
  isMaximal s a ↔ isMaximalQ s (Quotient.mk s.setoid a) := by
  constructor
  · --------------------
    -- (→) 方向の証明
    intro ha  -- `ha` : a は元の前順序で極大
    intro x hx
    -- x は商集合上の元なので、代表元 b を取り出す
    rcases Quotient.exists_rep x with ⟨b, rfl⟩
    -- hx : Quotient.mk a ≤ Quotient.mk b から a ≤ b を得る
    dsimp [isMaximal] at ha
    specialize ha b
    have : a ≤ b := by
      exact pullback_preorder_lemma s (Quotient.mk s.setoid a) (Quotient.mk s.setoid b) a b rfl rfl hx
    have : b ≤ a := by
      exact ha this
    apply pushforward_preorder_lemma s
    simp_all only [imp_self]
  · --------------------
    -- (←) 方向の証明
    intro ha  -- `ha` : 商集合で Quotient.mk a が極大
    intro b hab
    -- a ≤ b から商集合でも Quotient.mk a ≤ Quotient.mk b となる
    dsimp [isMaximalQ] at ha
    have : s.po.le (Quotient.mk s.setoid a) (Quotient.mk s.setoid b) := by
      exact pushforward_preorder_lemma s a b hab
    have : s.po.le (Quotient.mk s.setoid b) (Quotient.mk s.setoid a) := by
      simp_all only [imp_self]
    apply pullback_preorder_lemma s ⟦b⟧ ⟦a⟧ b a rfl rfl
    simp_all only

/--
「元の前順序での極大元の集合」-
「商集合上での極大元の集合」とが、商写像 `Quotient.mk` を通じて
ちょうど同じものになる、ということを集合レベルでも示せます。
-/
noncomputable def MaxSet (s:Setup2 α) := ({ a : s.V | isMaximal s a }:Finset s.V)
noncomputable def MaxQuotSet (s:Setup2 α) : Finset (Quotient (s.setoid)) :=
  { x : Quotient s.setoid | isMaximalQ s x }

lemma MaxQuotSet_eq_image (s:Setup2 α) :
  MaxQuotSet s = Finset.image (Quotient.mk (s.setoid)) (MaxSet s) := by
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
      simp_all only [mem_attach, and_self]
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
      simp_all only [mem_attach, true_and]
      obtain ⟨val, property⟩ := b
      obtain ⟨val_1, property_1⟩ := a
      rw [isMaximal_iff] at ha
      apply ha
      simp_all only

--残った示すべきことは、半順序のほうで、
--各ノードに対して、唯一の極大元が存在するということがわかればよい。
--極大元の存在は比較的簡単。
--二つあったら一致することも証明できる。
--あと、setupを使って、ideal集合族が一致することを示す必要があるかも。


/-
--Quotientとどう違う。多分古いもの。動くかどうかは未確認。
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
  have h_eq_class : eqClass V x.val = Finset.image (λ v => v) {v | f v = x.val} ∪ ({x}:Finset V) := by
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

--def fiterate (s: Setup α) (x : α) (n : ℕ) : α :=
--  s.f^[n] x
