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


lemma isMaximal_iff (s: Setup2 α) (a : s.V) :
  isMaximal s.toSetup a ↔ isMaximalQ s (Quotient.mk s.setoid a) := by
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
noncomputable def MaxSet (s:Setup2 α) := ({ a : s.V | isMaximal s.toSetup a }:Finset s.V)
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

/-- 有限の半順序集合において、任意の元 `x` に対し `x ≤ y` かつ `y` が極大な元 `y` が存在する -/
theorem exists_max_ge_of_mem {s : Setup2 α} {q : Quotient s.setoid} :
  ∃ y : Quotient s.setoid, s.po.le q y ∧ ∀ z : Quotient s.setoid, s.po.le y z → z = y :=
by
  let uA:Finset (Quotient s.setoid) := univ
  let A := uA.filter (fun z => s.po.le q z)


  have hA_nonempty : A.Nonempty := ⟨q, by simp_all only [mem_filter, Finset.mem_univ, le_refl, and_self, A, uA]⟩

  obtain ⟨m, hmA, hmax⟩ := Finset.exists_maximal A hA_nonempty
  have hms : m ∈ uA := by simp_all only [mem_filter, Finset.mem_univ, true_and, A, uA]--mem_of_mem_filter hmA
  have hxm : s.po.le q m := by simp_all only [mem_filter, Finset.mem_univ, true_and, A, uA]

  use m
  constructor
  · exact hxm
  · intro z
    intro h
    let hmaxz := hmax z
    simp at hmaxz
    have notspo: ¬ (s.po.lt m z) :=
    by
      simp_all only [mem_filter, Finset.mem_univ, and_self, A, uA]
      apply Aesop.BuiltinRules.not_intro
      intro a
      apply hmaxz
      · simp_all only [mem_filter, Finset.mem_univ, true_and, A, uA]
        exact le_trans hxm h
      · simp_all only [A, uA]

    have : z ∈ A:=
    by
      simp_all only [mem_filter, Finset.mem_univ, and_self, true_and, A, uA]
      exact le_trans hxm h
    specialize hmaxz this
    --rw  [s.h_po] at h  --rwできるがやらない方が良かったみたい。
    --rw [partialOrder_from_preorder] at h
    --なんだかよくわからないけど、証明できたパターン。不等式の分解が難しい。
    --po.ltをleで書き直した。
    have : ¬((¬s.po.le z m) ∧ s.po.le m z) := --これはhmaxzと同値なはず。
    by
      rw [s.h_po]
      rw [partialOrder_from_preorder]
      rw [s.h_po] at notspo
      rw [partialOrder_from_preorder] at notspo
      simp_all only [mem_filter, Finset.mem_univ, and_self, true_and, Decidable.not_not, not_false_eq_true,
        not_true_eq_false, and_true, A, uA]
      simp_all only [not_and, Decidable.not_not, A, uA]
      intro a
      simp_all only [imp_false, not_false_eq_true, A, uA]
    rw [not_and_or] at this
    simp at this
    cases this with
    |inl hh =>
      apply s.po.le_antisymm
      exact hh
      exact h
    |inr hh =>
      rename_i h
      exfalso
      exact hh h

--同値類間の写像。
/-
def fq (s: Setup2 α) (q:(Finset.univ:Finset (Quotient s.setoid))):
  (Finset.univ:Finset (Quotient s.setoid)) :=
by

  let ql := Quotient.lift (fun (x:s.V) => Quotient.mk s.setoid (s.f x))
    (by
      intros a b h
      -- まず setoid の定義を展開
      dsimp [Quotient.lift]
      rw [@Quotient.eq]
      exact (Setoid.comap_rel s.f s.setoid a b).mp h
    )
  --simp_all only [Finset.mem_univ]
  obtain ⟨val, property⟩ := q
  --simp_all only [Finset.mem_univ]
  use val
-/
-------------------------------------------------------------
--同じ同値類のfの行き先は、同値になることを示す必要がある。
lemma f_on_equiv
  (s: Setup2 α) (x y: s.V) (h: s.setoid.r x y) :
  s.setoid.r (s.f x) (s.f y) :=
by
  have eqy: eqClass_setup s.toSetup x = eqClass_setup s.toSetup y := by
      apply eqClass_eq
      · rw [s.h_setoid] at h
        rw [setoid_preorder] at h
        simp [equiv_rel] at h
        simp_all only
      · rw [s.h_setoid] at h
        rw [setoid_preorder] at h
        simp [equiv_rel] at h
        simp_all only
  have xineq: x∈ eqClass_setup s.toSetup x := by
          simp_all only [eqClass_setup]
          simp
          rw [s.h_setoid]
          rw [setoid_preorder]
          simp [equiv_rel]
          rw [s.h_setoid] at h
          rw [setoid_preorder] at h
          simp [equiv_rel] at h
          simp_all only [ge_iff_le, not_le, and_self]

  have yineq: y ∈ eqClass_setup s.toSetup x := by
      simp_all only [eqClass_setup]
      rw [s.h_setoid] at h
      rw [setoid_preorder] at h
      simp [equiv_rel] at h
      simp_all only [mem_filter, mem_attach, true_and]
      rfl

  by_cases h1: (eqClass_setup s.toSetup x).card ≥ 2;
  case pos =>
    let eqsx := eqClass_size_ge_two_implies_outside s.toSetup x h1
    have : s.f x ∈ eqClass_setup s.toSetup x := by
      simp_all only [eqsx]
      rwa [← eqy]
    have : s.f y ∈ eqClass_setup s.toSetup y := by
      have :(eqClass_setup s.toSetup y).card ≥ 2 := by
        rw [←eqy]
        exact h1
      exact eqClass_size_ge_two_implies_outside s.toSetup y this
    rw [←eqy] at this
    rw [s.h_setoid]
    rw [setoid_preorder]
    simp
    dsimp [equiv_rel]
    let eqe := (eqClass_eq_rev s.toSetup (s.f x) (s.f y) x)
    specialize eqe eqsx
    specialize eqe this
    constructor
    · exact eqe.1
    · exact eqe.2
  case neg =>
    --同値類の大きさが1のとき。
    --同値類の大きさが1であれば、同値のものは一致する。
    have :(eqClass_setup s.toSetup x).card = 1 := by
      --cardは1以上で2以上でないので、ちょうど1になる。
      have geq1:(eqClass_setup s.toSetup x).card ≥ 1 := by

        have :(eqClass_setup s.toSetup x).Nonempty := by
          simp_all only [ge_iff_le, not_le]
          exact ⟨_, xineq⟩
        exact Finset.card_pos.mpr this
      have leq1: (eqClass_setup s.toSetup x).card  ≤ 1 := by
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

--setoidの半順序の一つ上のQuotientを指すもの。
def fq (s: Setup2 α) (q:(Quotient s.setoid)):
  (Quotient s.setoid) :=
 Quotient.lift (fun (x:s.V) => Quotient.mk s.setoid (s.f x))
    (by
      intros a b h
      -- まず setoid の定義を展開
      dsimp [Quotient.lift]
      rw [@Quotient.eq]
      apply (Setoid.comap_rel s.f s.setoid a b).mp
      have :s.setoid a b := by
        exact h
      rw [← @Quotient.eq_iff_equiv] at h
      let foe := f_on_equiv s a b this
      simp_all only [Quotient.eq]
      exact foe
    ) q

--Quotientとってからfqを施しても、fをとってからQuotientを取っても同じ。
lemma f_on_equiv_n
  (s: Setup2 α) (x : s.V) :
  ∀ n:Nat, Quotient.mk s.setoid (s.f^[n] x) = (fq s)^[n] (Quotient.mk s.setoid x) :=
by
  intro n
  induction n generalizing x
  case zero =>
    simp_all only [Finset.mem_univ, Quotient.lift_mk, Quotient.mk]
    simp_all only [Function.iterate_zero, id_eq]
  case succ n ih =>
    simp_all only [Function.iterate_succ, Quotient.mk]
    rw [@Function.comp_def]
    rw [@Function.comp_def]
    rw [ih (s.f x)]
    simp_all only [Subtype.forall]
    --obtain ⟨val, property⟩ := x
    congr 1

--引数に対応するFinsetで表した同値類。
noncomputable def equiv_class_finset (s: Setup2 α)(a : s.V) : Finset s.V := { x : s.V | s.setoid.r a x}.toFinset
--Quotientを集合表現に。
noncomputable def quotient_to_finset (s: Setup2 α) (q : Quotient (s.setoid )) : Finset s.V :=
  Quotient.liftOn q (fun a => equiv_class_finset s a)
    (by
      intros a b h
      -- まず setoid の定義を展開
      dsimp [Quotient.liftOn]
      --let sc := (Setoid.comap_rel s.f s.setoid a b)
      dsimp [equiv_class_finset]
      ext x
      constructor
      · intro h1
        simp
        simp at h1
        apply Setoid.trans' s.setoid
        · exact id (s.setoid.symm h)
        · simp_all only
      · intro h1
        simp
        simp at h1
        apply Setoid.trans' s.setoid
        · exact h
        · simp_all only
    )

--任意の同値類から要素を取れることも補題にする。
lemma quotient_representative (s: Setup2 α) (q: Quotient s.setoid) :
  ∃ x : s.V, q = Quotient.mk s.setoid x :=
by
  simp_all only [Subtype.exists]
  rcases q with ⟨x,hx⟩
  exact ⟨x, hx, rfl⟩

lemma pre_po_lemma (s: Setup2 α) (x y :s.V) :
 s.pre.le x y ↔ s.po.le (Quotient.mk s.setoid x) (Quotient.mk s.setoid y) := by
  constructor
  · intro h
    exact pushforward_preorder_lemma s x y h
  · intro h
    exact pullback_preorder_lemma s ⟦x⟧ ⟦y⟧ x y rfl rfl h

lemma f_fq_lemma (s: Setup2 α) (x:s.V) :
  ∀ n:Nat, Quotient.mk s.setoid (s.f^[n] x) = (fq s)^[n] (Quotient.mk s.setoid x) := by
  intro n
  induction n generalizing x
  case zero =>
    simp_all only [Finset.mem_univ, Quotient.lift_mk, Quotient.mk]
    simp_all only [Function.iterate_zero, id_eq]

  case succ n ih =>
    simp_all only [Function.iterate_succ, Quotient.mk]
    rw [@Function.comp_def]
    rw [@Function.comp_def]
    rw [ih (s.f x)]
    simp_all only [Subtype.forall]
    --obtain ⟨val, property⟩ := x
    congr 1

lemma fq_lemma (s: Setup2 α) (qx:Quotient s.setoid) :
  ∀ qy :(Quotient s.setoid), s.po.le qx qy → ∃ n:Nat, qy = ((fq s)^[n]) qx :=
by
  intro qy hqy
  obtain ⟨x, hx⟩ := quotient_representative s qx
  obtain ⟨y, hy⟩ := quotient_representative s qy
  have : s.pre.le x y := by
    rw [hx] at hqy
    rw [hy] at hqy
    apply pullback_preorder_lemma s qx qy x y
    subst hx hy
    simp_all only
    subst hx hy
    simp_all only
    subst hx hy
    simp_all only
  let il := iteratef_lemma_ref s.toSetup x y this
  obtain ⟨n, h⟩ := il
  use n

  let fone := f_on_equiv_n s x
  rw [←hx] at fone
  rw [←fone n]
  rw [hy]
  rw [←h]

--poからfqの大小の方向。fq_lemma_revのbase caseに使う。これの逆向きも必要かも。
lemma fq_lemma_rev_one (s: Setup2 α) (qx :Quotient s.setoid) :
  s.po.le qx ((fq s) qx) :=
by
  --pre_po_lemmaでs.preの議論に帰着する。
  --qxや((fq s) qx)の代表元を持ってくる必要。
  --そのあと、f_on_equiv_revを使う？
  obtain ⟨x,hx⟩ := quotient_representative s qx
  --obtain ⟨y,hy⟩ := quotient_representative s ((fq s) qx)
  let y := s.f x
  have hy: ((fq s) qx) = Quotient.mk s.setoid y := by --どこかで示したかも。
    rw [@Setup.h_setoid] at qx
    rw [setoid_preorder] at qx
    simp_all only [Quotient.lift_mk]
    subst hx
    simp_all only [y]
    rfl
  let ppl := pre_po_lemma s x y
  have : s.pre.le x y := by
    dsimp [y]
    exact f_and_pre s.toSetup x (s.f x) rfl
  subst hx
  simp_all [y]

lemma fq_lemma_rev (s: Setup2 α) (qx qy:Quotient s.setoid) :
  (∃ n:Nat, qy = ((fq s)^[n]) qx) → s.po.le qx qy :=
by
  intro h
  obtain ⟨n, h⟩ := h
  rw [h]
  induction n generalizing qx
  case zero =>
    subst h
    simp_all only [Function.iterate_zero, id_eq, le_refl]
  case succ n ih =>
    subst h
    simp_all only [Function.iterate_succ, Quotient.mk]
    rw [@Function.comp_def]
    --rw [ih (s.f x)]
    simp_all only [Subtype.forall]
    --s.po qx (fq s qx)
    --s.po (fq s qx) (fq s)^[n]
    --を証明して、推移律か。
    have : s.po.le qx ((fq s) qx) := by
      apply fq_lemma_rev_one
    --have : s.po.le ((fq s) qx) ((fq s)^[n] qx) := by
    let ihh := ih (fq s qx)
    simp_all only [ge_iff_le]
    apply le_trans
    · exact this
    · simp_all only [Function.comp_apply]

--次やるべきことは、同値類の大小関係とfqの写像の関係。


--残った示すべきことは、半順序のほうで、
--各ノードに対して、唯一の極大元が存在するということがわかればよい。
--極大元の存在は比較的簡単。
--二つあったら一致することも証明できる。
--あと、setupを使って、ideal集合族が一致することを示す必要があるかも。

/-
多分古いもの。動くかどうかは未確認。
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
