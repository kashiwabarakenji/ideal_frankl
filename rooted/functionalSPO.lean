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
--import rooted.functionalTreePreorder
import rooted.functionalTreePartialorder

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

def reach {A : Type} (f : A → A) (x y : A) : Prop :=
  ∃ n : ℕ, f^[n] x = y

def partialOrderOfFq {A : Type} (f : A → A)
  (noLoop : ∀ x y, reach f x y → reach f y x → x = y)
  : PartialOrder A :=
{ le := reach f
  le_refl := by
    intro x
    dsimp [reach]
    use 0
    simp_all only [Function.iterate_zero, id_eq]

  le_trans := by
      intro x y z ⟨n, hn⟩ ⟨m, hm⟩
      exists (n + m)
      subst hn hm
      let fi := (Function.iterate_add_apply f m n x)
      rw [add_comm] at fi
      exact fi

  , le_antisymm := by
      intro x y hxy hyx
      exact noLoop x y hxy hyx
}

structure Setup_spo (α : Type) [Fintype α] [DecidableEq α] where
  (V : Finset α)
  (nonemp   : V.Nonempty)
  (setoid : Setoid {x : α // x ∈ V})
  (fq : Quotient setoid → Quotient setoid)
  -- antisymmetry を保証する仮定：ループがあれば自明なもののみ
  (noLoop : ∀ x y : Quotient setoid,
    (reach fq x y → reach fq y x → x = y))
  (spo : PartialOrder (Quotient setoid))
  (h_spo : spo = partialOrderOfFq fq noLoop)

def isMaximal_spo (s: Setup_spo α) (x : Quotient s.setoid) : Prop :=
  ∀ y : Quotient s.setoid,
  s.spo.le x y → s.spo.le y x

def classOf (s : Setup_spo α) (q : Quotient s.setoid) [DecidableEq (Quotient s.setoid)]  : Finset {x // x ∈ s.V} :=
  Finset.filter (fun (a : {x // x ∈ s.V}) => @Quotient.mk'' _ s.setoid a = q) s.V.attach

structure Setup_spo2 (α : Type) [Fintype α] [DecidableEq α]
  extends Setup_spo α where
  -- 極大でない要素の同値類のサイズが 1
  singleton_if_not_maximal :
    ∀ q : Quotient toSetup_spo.setoid,
      ¬ isMaximal_spo toSetup_spo q →
      (classOf toSetup_spo q).card = 1

lemma reach_leq (s : Setup_spo α) (x y : Quotient s.setoid) :
  reach s.fq x y → s.spo.le x y := by
  --これはs.spo.leの定義な気もするが。
  intro h
  rw [s.h_spo]
  dsimp [partialOrderOfFq] at *
  exact h

lemma reach_leq2 (s : Setup2 α) (x y : Quotient s.setoid) :
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

def setup_setupspo (s: Setup2 α) : Setup_spo α :=
{
  V := s.V,
  nonemp := s.nonemp,
  setoid := s.setoid,
  fq := fq s
  noLoop := by
    have : ∀ x y : Quotient s.setoid, (reach (fq s) x y → reach (fq s) y x → x = y) := by
      intro x y hxy hyx
      dsimp [reach] at *
      --let n := ((fq s)^[0] x)
      --let m := ((fq s)^[0] y)
      obtain ⟨n, hn⟩ := Quotient.exists_rep x
      obtain ⟨m, hm⟩ := Quotient.exists_rep y
      --nとmが同じであることはない。同じだとx=yになる。
      --xとyが違う同値類としてよい。
      --でも、x <= yと y <= xのときは、antisymmetryからx=yになる。
      have : x ≤ y := reach_leq2 s x y hxy
      have : y ≤ x := reach_leq2 s y x hyx
      apply s.po.le_antisymm

    exact this,
  spo := partialOrderOfFq (fq s) (by
    have : ∀ x y : Quotient s.setoid, (reach (fq s) x y → reach (fq s) y x → x = y) := by
      intro x y hxy hyx
      dsimp [reach] at *
      have : s.po.le x y  = reach (fq s) x y := by
        let rl := reach_leq2 s x y hxy
        simp_all only [eq_iff_iff, true_iff, rl]
        obtain ⟨w, h⟩ := hxy
        obtain ⟨w_1, h_1⟩ := hyx
        subst h
        rw [← h_1]
        simp_all only
        rw [reach]
        simp_all only [exists_apply_eq_apply]
      have poxy: s.po.le x y := by
        dsimp [reach] at this
        rw [this]
        exact hxy
      have : s.po.le y x = reach (fq s) y x := by
        let rl := reach_leq2 s y x hyx
        simp_all only [eq_iff_iff, true_iff, rl]
        obtain ⟨w, h⟩ := hxy
        obtain ⟨w_1, h_1⟩ := hyx
        subst h
        rw [← h_1]
        simp_all only
        rw [reach]
        exact Exists.intro w_1 h_1
      have poyx: s.po.le y x := by
        dsimp [reach] at this
        rw [this]
        exact hyx
      apply s.po.le_antisymm
      exact poxy
      exact poyx
    intro x y a a_1
    exact this _ _ a a_1)
  h_spo := rfl
}

-- 証明すべきこと
--1. setup2から得られるsetoidとpartialOrderは、Setup_spo2の定義を満たす。
--2. Setup_spo2から得られるideal全体の集合族において、極大の同値類の大きさが2以上のときに、1元traceしても、またSetup2になる。
--3. Setup_spo2から得られるideal全体の集合族において、極大元の同値類に属する要素は、rareである。
--4. 閉集合族において、パラレルな要素を持つrareな要素のtraceは、標準化次数和を上げる。
--5. Setup2から得られる集合族の極大元に対応する同値類の大きさがすべて1であるときは、idealの集合族は、台集合上の半順序(setup_po)のideal集合族に一致する。

def setup2_induces_spo (s : Setup2 α) : Setup_spo2 α :=
{
  V := s.V,
  nonemp := s.nonemp,
  setoid := s.setoid,
  fq := fq s
  noLoop := (setup_setupspo s).noLoop,
  spo := (setup_setupspo s).spo,
  h_spo := (setup_setupspo s).h_spo,
  singleton_if_not_maximal := by
    intro q hq
    dsimp [isMaximal_spo] at hq
    have : ¬ isMaximal_spo (setup_setupspo s) q := by
      intro h
      apply hq
      exact h
    dsimp [singleton_if_not_maximal] at this
    have : (classOf (setup_setupspo s) q).card = 1 := by
      apply this q
      exact this
    exact this

}
