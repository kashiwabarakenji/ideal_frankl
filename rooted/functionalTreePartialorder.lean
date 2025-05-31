--Setup2が定義される。
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

--ここで定義するsetup2は、同値類setoid上の半順序に関するもの。s.poやs.fqが使える。
--半順序で大小関係があったら、それをpullbackした前順序でも大小関係がある。
--前順序で大小関係があったら、それをpushforwardした半順序でも大小関係がある。
--preorderの大きさ2以上の同値類は、半順序の極大要素になる。(ここでは示してない？)
--preorderの極大要素は、同値類の極大要素になる。(ここでは示してない？)


-------------------
---Setup2の定義の準備
--------------------

--quotient_partial_orderよりも証明が長いのは、preorderが間接的に定義されているから？
-- Preorder_eq_PartialOrderでも利用されている。
-- 直接この定義を利用しなくても、このファイルの補題を通じて利用している。
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

/- 使ってなかった。
noncomputable def spullback  (s: Setup α) (J : Finset (Quotient s.setoid)) : Finset s.V :=
  { a : s.V | Quotient.mk s.setoid a ∈ J }

noncomputable def spushforward  (s: Setup α) (I : Finset s.V) : Finset (Quotient s.setoid) :=
  Finset.univ.filter (fun q => ∃ a ∈ I, Quotient.mk s.setoid a = q)
-/

--同値類上の半順序を加えたSetup。仮定としての強さは、Setupと同じか。するとSetupからSetup2が定義できる。Setup_to_Setup2
--Setup2にすることで、s.poが使える。
--リファクタリング予定：SetupとSetup2にわけないで、poをdefにしてしまったほうがよかった。
--上のinstanceは、s.po.leとは別物になってしまうので、instanceでなくてdefのほうがよい。
structure Setup2 (α : Type) [Fintype α] [DecidableEq α] extends Setup α where
  (po       : PartialOrder (Quotient setoid))
  (h_po     :  po = partialOrder_from_preorder toSetup)

--前に定義していたquotient_partial_orderと内容的に被っている。
instance (s : Setup2 α) : PartialOrder (Quotient s.setoid) := s.po

--SetupとSetup2は仮定としての強さが同じ。
def Setup_to_Setup2 (s : Setup α) : Setup2 α :=
  {
    nonemp := s.nonemp
    valid := s.valid
    h_pre := s.h_pre
    h_setoid := s.h_setoid
    po := partialOrder_from_preorder s
    h_po := rfl
  }

/-
--これは自明なのか。使ってないのでコメントアウト。
lemma setup_to_setup2_prop (s : Setup α) :
 (Setup_to_Setup2 s).toSetup = s :=
by
  exact rfl
-/

------------------------
--s.preとs.poの関係を示す補題。
---------------------------

--同値類は、大小関係と両立する。下で使っているし外からも使っている。
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

--要素の大小関係と、同値類の大小関係の関係。下で使っているし、そとからも使っている。
--逆方向は、上の補題？
--Preorder_eq_PartialOrderなどで利用。
lemma pushforward_preorder_lemma (s : Setup2 α) (x1 x2 : s.V) :
  s.pre.le x1 x2 → s.po.le (Quotient.mk s.setoid x1)  (Quotient.mk s.setoid x2) :=
by
  intro h
  rw [@Setup2.h_po]
  dsimp [partialOrder_from_preorder]
  simp_all only

--------------------------
-- 極大要素に関する定義や補題。

--商集合上 `(Quotient setoid_preorder, ≤)` における「極大元」であることを表す述語。
--この順序はPartial orderの順序。まだ使ってないかも。setupで書き直す。
def isMaximalQ (s : Setup2 α) (x : Quotient (s.setoid)) : Prop :=
  ∀ y, s.po.le x y → s.po.le y x

--要素としての極大性と、同値類の極大性の関係。別のファイルで使っている。
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

-------------------
----fqに関係する補題。
--------------------

--setoidの半順序の一つ上のQuotientを指すもの。
--Setup2じゃなくて、Setupにすることもできるかもしれないが。
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
      let foe := f_on_equiv s.toSetup a b this
      simp_all only [Quotient.eq]
      exact foe
    ) q

--Quotientとってからfqを施しても、fをとってからQuotientを取っても同じ。
--fqの引数がSetupでなくて、Setup2にする必要あり。reachを使えそう。
private lemma f_on_equiv_n
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

--任意の同値類から要素を取れることも補題にする。Setupでも良さそうだが、ここでしか使わないので。Quot.outでもよさそう。
private lemma quotient_representative (s: Setup2 α) (q: Quotient s.setoid) :
  ∃ x : s.V, q = Quotient.mk s.setoid x :=
by
  simp_all only [Subtype.exists]
  rcases q with ⟨x,hx⟩
  exact ⟨x, hx, rfl⟩

--下で利用。
private lemma pre_po_lemma (s: Setup2 α) (x y :s.V) :
 s.pre.le x y ↔ s.po.le (Quotient.mk s.setoid x) (Quotient.mk s.setoid y) := by
  constructor
  · intro h
    exact pushforward_preorder_lemma s x y h
  · intro h
    exact pullback_preorder_lemma s ⟦x⟧ ⟦y⟧ x y rfl rfl h

/-
--reachを使えそう。f_on_equiv_nと同じだった。
lemma f_fq_lemma (s: Setup2 α) (x:s.V) :
  ∀ n:Nat, Quotient.mk s.setoid (s.f^[n] x) = (fq s)^[n] (Quotient.mk s.setoid x) := by
  intro n
  exact f_on_equiv_n s x n
-/
  /-
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
  -/

--reachを使って書き直せる？逆は、fq_lemma_rev。
--そとからも使っている。
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

--poからfqの大小の方向。fq_lemma_revのbase caseに使う。
--1段階の場合。
--下で使っている。
private lemma fq_lemma_rev_one (s: Setup2 α) (qx :Quotient s.setoid) :
  s.po.le qx ((fq s) qx) :=
by
  --pre_po_lemmaでs.preの議論に帰着する。
  --qxや((fq s) qx)の代表元を持ってくる必要。
  --そのあと、f_on_equiv_revを使う？

  obtain ⟨x,hx⟩ := quotient_representative s qx

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

--fqのiterationでいけるものは、大小関係がある。fq_lemmaの逆。
--functionalSPOでreachを使って書き換えられるreach_leq のでそっちを使うと良い。
--外から使っていた。
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

    simp_all only [Subtype.forall]

    have : s.po.le qx ((fq s) qx) := by
      apply fq_lemma_rev_one

    let ihh := ih (fq s qx)
    simp_all only [ge_iff_le]
    apply le_trans
    · exact this
    · simp_all only [Function.comp_apply]

--こっちは、spoでなくてpoの方。外でも使っている。名前を変えた。
lemma reach_po_leq (s : Setup2 α) (x y : Quotient s.setoid) :
  reach (fq s) x y → s.po.le x y := by
  --これはs.spo.leの定義な気もするが。
  intro h
  rw [s.h_po]
  dsimp [reach] at h
  let fql := fq_lemma_rev s x y
  obtain ⟨n, hn⟩ := h
  rw [←hn]
  have :(∃ n, y = (fq s)^[n] x) := by
    use n
    subst hn
    simp_all only
  specialize fql this
  rw [←hn] at fql
  convert fql
  rw [s.h_po]

/-
--今のところ使ってない？極大なものより大きなものは下に一致。
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
-/

--同値類間の写像。
/- Setupの中に組み込まれているから必要ないかも。
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
