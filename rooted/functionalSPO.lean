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
--以下とほぼ同じ
--noncomputable def eqClass_setup (s: Setup α) (x : {x : α // x ∈ s.V}) : Finset {x // x ∈ s.V} :=
--  s.V.attach.filter (fun y => s.setoid.r x y)

structure Setup_spo2 (α : Type) [Fintype α] [DecidableEq α]
  extends Setup_spo α where
  -- 極大でない要素の同値類のサイズが 1
  singleton_if_not_maximal :
  ∀ q : Quotient toSetup_spo.setoid,
    (classOf toSetup_spo q).card ≥ 2 →
    isMaximal_spo toSetup_spo q

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
    have : ∀ q1 q2 : Quotient s.setoid, (reach (fq s) q1 q2 → reach (fq s) q2 q1 → q1 = q2) := by
      intro q1 q2 hxy hyx
      dsimp [reach] at *
      --let n := ((fq s)^[0] x)
      --let m := ((fq s)^[0] y)
      obtain ⟨x, hx⟩ := Quotient.exists_rep q1
      obtain ⟨y, hy⟩ := Quotient.exists_rep q2
      --nとmが同じであることはない。同じだとx=yになる。
      --xとyが違う同値類としてよい。
      --でも、x <= yと y <= xのときは、antisymmetryからx=yになる。
      have : q1 ≤ q2 := reach_leq2 s q1 q2 hxy
      have : q2 ≤ q1 := reach_leq2 s q2 q1 hyx
      apply s.po.le_antisymm
      · subst hy hx
        simp_all only
      · exact this

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

/-
  lemma eqClass_size_ge_two_implies_inverse
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup α)
    (x : {x // x ∈ s.V})
    (h : 2 ≤ (eqClass_setup s x).card) :
  ∀ y : {x // x ∈ s.V},  s.pre.le x y → s.pre.le y x := by
-/
/-lemma isMaximal_iff (s: Setup2 α) (a : s.V) :
  isMaximal s.toSetup a ↔ isMaximalQ s (Quotient.mk s.setoid a) := by
-/

lemma eqClass_Class_of (s: Setup2 α) (x : {x : α // x ∈ s.V}) :
  (eqClass_setup s.toSetup) x = classOf (setup_setupspo s) (@Quotient.mk' _ s.setoid x) := by
  dsimp [classOf]
  dsimp [eqClass_setup]
  dsimp [setup_setupspo]
  congr
  apply funext
  intro x
  rename_i x_1
  simp_all only [eq_iff_iff]
  obtain ⟨val, property⟩ := x_1
  obtain ⟨val_1, property_1⟩ := x
  apply Iff.intro
  · intro a
    symm
    exact Quotient.sound' a
  · intro a
    rw [Quotient.mk''_eq_mk] at a
    symm
    simp only [Quotient.mk'] at a
    simp_all only [Quotient.eq]

lemma eqClass_Class_of2 (s: Setup2 α) (q : Quotient s.setoid) :
  eqClass_setup s.toSetup (Quotient.out q) = (classOf (setup_setupspo s) q) :=
by
  rw [eqClass_Class_of]
  congr
  simp [Quotient.mk']

lemma spole_iff_po (s: Setup2 α) (x y : Quotient s.setoid) :
  s.po.le x y ↔ (setup_setupspo s).spo.le x y := by
  dsimp [setup_setupspo]
  dsimp [partialOrderOfFq]
  dsimp [reach]
  apply Iff.intro
  · intro h
    let fql := fq_lemma s x y h
    obtain ⟨n, hn⟩ := fql
    use n
    exact hn.symm
  · intro h
    obtain ⟨n, hn⟩ := h
    have :(∃ n, y = (fq s)^[n] x) := by
      use n
      subst hn
      simp_all only
    let fql := fq_lemma_rev s x y this
    exact fql

lemma isMaximal_spo_iff (s: Setup2 α) (q : Quotient s.setoid) :
  isMaximal_spo (setup_setupspo s) q ↔
  isMaximalQ s q :=
by
  dsimp [isMaximal_spo]
  dsimp [isMaximalQ]
  dsimp [setup_setupspo]
  apply Iff.intro
  · intro h
    intro y
    let hy := h y
    rw [spole_iff_po]
    rw [spole_iff_po]
    exact hy
  · intro h
    intro y
    let hy := h y
    rw [spole_iff_po] at hy
    rw [spole_iff_po] at hy
    exact hy

lemma eqClass_Maximal (s: Setup2 α) (q : Quotient s.setoid) :
  (classOf (setup_setupspo s) q).card ≥ 2 → isMaximalQ s q  := by
  intro h
  rw [←eqClass_Class_of2] at h
  dsimp [isMaximalQ]
  let ecs := eqClass_size_ge_two_implies_inverse s.toSetup (Quotient.out q) h
  obtain ⟨x, hx⟩ := Quotient.exists_rep q
  intro q2
  obtain ⟨y, hy⟩ := Quotient.exists_rep q2
  specialize ecs y
  let imi := isMaximal_iff s x
  rw [hx] at imi
  dsimp [isMaximal] at imi
  dsimp [isMaximalQ] at imi
  have: @Quotient.mk _ s.setoid q.out = q := by
    subst hy hx
    simp_all only [ge_iff_le, Subtype.forall, Quotient.out_eq]
  rw [←this]
  have : x ∈ eqClass_setup s.toSetup q.out := by
      dsimp [eqClass_setup]
      rw [Finset.mem_filter]
      constructor
      ·
        subst hy hx
        simp_all only [ge_iff_le, Subtype.forall, Quotient.out_eq, mem_attach]
      ·
        dsimp [eqClass_setup]
        rw [←hx]
        exact Quotient.mk_out x
  have q_eq : s.pre.le x q.out := by
    exact eqClass_ge s.toSetup q.out x this
  have q_eq2 : s.pre.le q.out x := by
    exact eqClass_le s.toSetup q.out x this
  rw [←hy]
  let imimp := imi.mp
  have : ∀ (b : { x // x ∈ s.V }), x ≤ b → b ≤ x := by
    intro b h
    have : q.out ≤ b := by
      exact Preorder.le_trans q.out x b q_eq2 h
    have : b ≤ q.out := by
      apply eqClass_size_ge_two_implies_inverse s.toSetup q.out
      subst hy hx
      simp_all only [ge_iff_le, Quotient.out_eq]
      subst hy hx
      simp_all only [ge_iff_le, Quotient.out_eq]
    exact Preorder.le_trans b q.out x this q_eq2
  specialize imimp this
  intro a
  subst hy hx
  simp_all only [Subtype.forall, ge_iff_le, Subtype.coe_eta, implies_true, Quotient.out_eq]

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
    let csm := eqClass_Maximal s q hq
    dsimp [isMaximalQ] at csm
    dsimp [isMaximal_spo]
    intro y h
    specialize csm y
    dsimp [setup_setupspo] at h
    dsimp [partialOrderOfFq] at h
    have : s.po.le q y := by
      simp_all only [ge_iff_le]
      exact reach_leq2 s q y h
    specialize csm this
    --let rl2 := reach_leq2 s q y h
    --simp_all only [ge_iff_le, rl2]
    rw [spole_iff_po] at csm
    exact csm
}
  --singleton_if_not_maximal := by
  --  intro q hq
  --  dsimp [isMaximal_spo] at hq
  --  let csm := eqClass_Maximal s q hq
  --  dsimp [isMaximalQ] at csm
  --  dsimp [isMaximal_spo]
  --  intro y h
  --  specialize csm y
  --  dsimp [setup_setupspo] at h
  --  dsimp [partialOrderOfFq] at h
  --  have : s.po.le q y := by}
