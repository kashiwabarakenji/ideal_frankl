import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Quot
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

--fqまで定義すれば同値類上の前順序が定まる。loopがないことまで証明して半順序。
structure Setup_spo_base (α : Type) [Fintype α] [DecidableEq α] where
  (V : Finset α)
  (nonemp   : V.Nonempty)
  (setoid : Setoid {x : α // x ∈ V})
  (fq : Quotient setoid → Quotient setoid)

--ここでのfqはSetup_spo_baseのfq。
structure Setup_spo (α : Type) [Fintype α] [DecidableEq α] extends Setup_spo_base α where
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

lemma reach_leq (s : Setup_spo α) (x y : Quotient s.setoid) :
  reach s.fq x y → s.spo.le x y := by
  --これはs.spo.leの定義な気もするが。
  intro h
  rw [s.h_spo]
  dsimp [partialOrderOfFq] at *
  exact h


lemma reach_leq_rev (s : Setup_spo α) (x y : Quotient s.setoid) :
  s.spo.le x y →  reach s.fq x y  := by
  intro h
  rw [s.h_spo] at h
  dsimp [partialOrderOfFq] at h
  dsimp [reach]
  exact h

  --こっちは、spoでなくてpoの方。
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

--fq_lemmaと内容が被っている。
lemma reach_leq2_rev (s : Setup2 α) (q1 q2 : Quotient s.setoid) :
  s.po.le q1 q2 → reach (fq s) q1 q2 :=
by
  --rw [s.h_po]これをするとfq_lemmaに適用できない。
  dsimp [reach]
  intro h
  let fql := fq_lemma s q1 q2 h
  obtain ⟨n, hn⟩ := fql
  use n
  exact hn.symm

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

--eqClassとclassOfは同じもの。
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

--上とほぼ同じだが、qを与えたもの。
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

--Setup_spo2から得られるideal全体の集合族において、同値類の大きさが2以上のときに、1元traceしても、またSetup2になる。
--同値類の要素は、パラレルであることは事前に示した方がいいのか。

def restrictedSetoid (s: Setup_spo α)(x : {x : α // x ∈ s.V}): Setoid {y : α // y ∈ s.V.erase x.val} :=
  Setoid.comap
    (fun y => ⟨y.val, Finset.mem_of_mem_erase y.property⟩)
    s.setoid

--新旧の同値類同士は全単射するので、fqを定義するには、それの対応の写像を作る必要がある。
def toOld (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  : Quotient (restrictedSetoid s x) → Quotient s.setoid :=
  λ newCls =>
    Quotient.liftOn newCls
      (fun (y : {y : α // y ∈ s.V.erase x.val}) =>
        -- y はもともと s.V に属するし，x とは違う
        @Quotient.mk _ s.setoid (⟨y.val, by exact Finset.mem_of_mem_erase y.property⟩ : {z // z ∈ s.V})
      )
      -- liftOn の証明義務：代表の取り方が違っても結果が同値類の同じ要素に行くこと
      (by
        intros a b hab
        apply Quotient.sound
        -- restrictedSetoid で同値 ⇒ もともとの setoid でも同値
        exact hab
      )

--同じ同値類から取ってきているという情報は次の補題を使う。
noncomputable def representativeNeSelf
  (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s ⟦x⟧).card ≥ 2) :
    { y // y ∈ s.V.erase ↑x } :=
  have h' : ∃ b ∈ classOf s ⟦x⟧, b ≠ x := exists_ne_of_one_lt_card hx x
  let b := Classical.choose (exists_ne_of_one_lt_card hx x)
  have hb := Classical.choose_spec (exists_ne_of_one_lt_card hx x)
  ⟨b, by
    simp only [Finset.mem_erase]
    exact ⟨Subtype.coe_ne_coe.mpr hb.right, b.property⟩⟩

lemma representativeNeSelf_mem_classOf
  (s : Setup_spo α) (x : {x // x ∈ s.V}) (hx : 2 ≤ (classOf s ⟦x⟧).card) :
  ⟨(representativeNeSelf s x hx).val, Finset.mem_of_mem_erase (representativeNeSelf s x hx).property⟩ ∈ (classOf s (@Quotient.mk _ s.setoid x)).erase x :=
by
  dsimp [representativeNeSelf]
  have hb := Classical.choose_spec (exists_ne_of_one_lt_card hx x)
  simp_all only [ne_eq, Subtype.coe_eta, mem_erase, not_false_eq_true, and_self]

lemma representativeNeSelf_mem_classOf2
  (s : Setup_spo α) (x : {x // x ∈ s.V}) (hx : 2 ≤ (classOf s ⟦x⟧).card) :
  s.setoid.r ⟨(representativeNeSelf s x hx), by
  obtain ⟨val, property⟩ := x
  simp_all only
  simp [representativeNeSelf]⟩ x :=
by
  dsimp [representativeNeSelf]
  have hb := Classical.choose_spec (exists_ne_of_one_lt_card hx x)
  simp_all only [ne_eq, Subtype.coe_eta, mem_erase, not_false_eq_true, and_self]
  dsimp [classOf] at hb
  rw [Finset.mem_filter] at hb
  obtain ⟨h1,h2⟩ := hb
  obtain ⟨h11,h12⟩ := h1
  exact Quotient.eq''.mp h12

--s.Vからs.V.erase xへの要素の対応。
noncomputable def toErased (s : Setup_spo α)
  (x : {x : α // x ∈ s.V})
  (hx : (classOf s ⟦x⟧).card ≥ 2) :
  { y // y ∈ s.V } → { y // y ∈ s.V.erase x } :=
  fun z =>
    if h : z = x then
      let z' := representativeNeSelf s x hx
      ⟨z'.val, by
        simp [Finset.mem_erase]

      ⟩
    else
      ⟨z.val, by
        simp [Finset.mem_erase, h]
        exact Subtype.coe_ne_coe.mpr h⟩

--toErasedの写像は、xと異なる場合は、恒等写像。
lemma toErased_eq_ne
  (s : Setup_spo α) (x z : {x // x ∈ s.V})
  (hx : 2 ≤ (classOf s ⟦x⟧).card)
  (h : z ≠ x) :
  toErased s x hx z = ⟨z.val, by
    simp [Finset.mem_erase]
    exact Subtype.coe_ne_coe.mpr h⟩ :=
by
  unfold toErased
  simp only
  split
  · contradiction
  · rfl

--一方xとyが同値で、xとzが同値のときに、yとzが同値なので、yの写り先とzの写り先も同値である。
/-
lemma Quotient.eq
  (s : Setup_spo2 α) (y z : {x : α // x ∈ s.V})
  (eq: s.setoid.r y z):
  @Quotient.mk _ s.setoid y = @Quotient.mk _ s.setoid z :=
by
  simp_all only [Quotient.eq]
-/
-- yとzが同じ同値類であれば、移り先も同じ同値類。
lemma toErased_eq
  (s : Setup_spo α) (x y z : {x : α // x ∈ s.V})
  (hx : 2 ≤ (classOf s ⟦x⟧).card)
  (q_eq:@Quotient.mk _ s.setoid y = @Quotient.mk _ s.setoid z):
   @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx y) = @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx z) :=
by
  dsimp [toErased]
  split
  · split
    ·
      rename_i h h_1
      subst h_1 h
      simp_all only [Subtype.coe_eta]
    · have a_eq_r: (toErased s x hx y) = (representativeNeSelf s x hx) := by
          --dsimp [representativeNeSelf]
          dsimp [toErased]
          simp
          rename_i h h_1
          intro h_2
          subst h
          ext : 1
          simp_all only
          simp_all only [not_true_eq_false]
      have : @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx y) = @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx z) :=
      by
        dsimp [toErased]
        dsimp [restrictedSetoid]
        simp
        rename_i h_1
        simp only [h_1]
        split_ifs with h_2
        · rename_i h
          subst h
          simp_all only [Quotient.eq]
        .
          rename_i h
          --使っているかも。
          have : s.setoid.r y z := by
            subst h
            simp_all only [Quotient.eq, not_false_eq_true]
          let rsx :=(⟨representativeNeSelf s x hx, by
              subst h
              simp_all only [Quotient.eq, not_false_eq_true]
              obtain ⟨val, property⟩ := y
              obtain ⟨val_1, property_1⟩ := z
              simp_all only [Subtype.mk.injEq]
              rw [← a_eq_r]
              simp_all only
              erw [← a_eq_r]
              simp_all only
              exact coe_mem _
            ⟩: { x // x ∈ s.V })
          have : s.setoid.r rsx y := by
            dsimp [rsx]
            let rmc2 := representativeNeSelf_mem_classOf2 s x hx
            subst h
            simp_all only [Quotient.eq, not_false_eq_true]
          have : s.setoid.r rsx z := by
            apply s.setoid.iseqv.trans
            · dsimp [rsx]
              let rmc2 := representativeNeSelf_mem_classOf2 s x hx
              subst h
              exact rmc2
            · dsimp [rsx]
              subst h
              simp_all only [Quotient.eq, not_false_eq_true, rsx]
          subst h
          simp_all only [Quotient.eq, rsx]

          exact this
      rw [a_eq_r] at this
      rw [this]
      simp

      dsimp [restrictedSetoid]
      dsimp [Setoid.comap]
      dsimp [toErased]
      rename_i h h_1
      subst h
      simp_all only [Quotient.eq, ↓reduceDIte]
      obtain ⟨val, property⟩ := y
      obtain ⟨val_1, property_1⟩ := z
      simp_all only
      rfl
  · split
    · --上の議論でyとzを取り替えたもので、同じもの。
      have a_eq_r: (toErased s x hx z) = (representativeNeSelf s x hx) := by
          dsimp [toErased]
          simp
          rename_i h h_1
          intro h_2
          subst h_1
          ext : 1
          simp_all only
          exact False.elim (h_2 rfl)
      have : @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx y) = @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx z) :=
      by
        dsimp [toErased]
        dsimp [restrictedSetoid]
        simp
        rename_i h_1

        simp only [h_1]
        split_ifs
        · rename_i h
          have : s.setoid.r y z := by
            subst h_1
            simp_all only [Quotient.eq]
          let rsx :=(⟨representativeNeSelf s x hx, by
              simp_all only [Quotient.eq, not_false_eq_true]
              obtain ⟨val, property⟩ := y
              obtain ⟨val_1, property_1⟩ := z
              rw [← a_eq_r]
              simp_all only
              erw [← a_eq_r]
              simp_all only
              exact coe_mem _
            ⟩: { x // x ∈ s.V })
          have : s.setoid.r rsx y := by
            dsimp [rsx]
            let rmc2 := representativeNeSelf_mem_classOf2 s x hx

            simp_all only [Quotient.eq, not_false_eq_true]
            exact
              Setoid.symm' s.setoid (Setoid.trans' s.setoid this (id (Setoid.symm' s.setoid rmc2)))
          have : s.setoid.r rsx z := by
            apply s.setoid.iseqv.trans
            · dsimp [rsx]
              let rmc2 := representativeNeSelf_mem_classOf2 s x hx
              exact rmc2
            · dsimp [rsx]
              simp_all only [Quotient.eq, not_false_eq_true, rsx]
              subst h_1
              rfl
          subst h_1
          simp_all only [rsx]

          dsimp [representativeNeSelf]
          tauto
      rw [a_eq_r] at this
      rw [←this]
      simp
      dsimp [restrictedSetoid]
      dsimp [Setoid.comap]
      dsimp [toErased]
      simp
      rename_i h_1
      subst h_1
      simp_all only [Quotient.eq, ↓reduceDIte]
      rfl
    ·
      simp_all only [Quotient.eq]
      exact q_eq

--古い同値類から新しい同値類への対応。
noncomputable def toNew (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2)
  : Quotient s.setoid → Quotient (restrictedSetoid s x) :=
  fun oldCls =>
    @Quotient.liftOn {x // x ∈ s.V} (Quotient (restrictedSetoid s x)) s.setoid oldCls
    (fun z => @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx z))
    (by
      intros a b hab
      apply toErased_eq s x a b hx
      simp_all only [ge_iff_le, Quotient.eq]
      exact hab
    )

--Newを行って、Oldを行うと元の同値類に戻る。
--いまいち、Quotient.inductionOnの使い方がわからないけど、証明できた。
lemma NewOld_id (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2)
  (Cls : Quotient s.setoid) :
  toOld s x (toNew s x hx Cls) = Cls := by
  induction Cls using Quotient.inductionOn
  case h a =>
    dsimp [toNew]
    dsimp [toOld]
    dsimp [toErased]
    --dsimp [restrictedSetoid]
    dsimp [representativeNeSelf]

    by_cases h:x ∈ (classOf s ⟦a⟧)
    case pos =>
      by_cases h_1 : a = x
      case pos =>
        subst h_1
        simp
        dsimp [classOf] at h
        rw [Finset.mem_filter] at h
        let cc := Classical.choose_spec (exists_ne_of_one_lt_card hx a)
        simp_all only [mem_attach, and_self]
        --obtain ⟨val, property⟩ := a
        obtain ⟨left, right⟩ := cc
        simp_all only [ne_eq]
        dsimp [classOf] at left
        rw [Finset.mem_filter] at left
        obtain ⟨left_1, right_1⟩ := left
        exact Quotient.eq''.mp right_1
      case neg =>
        dsimp [classOf] at h
        rw [Finset.mem_filter] at h
        obtain ⟨val, property⟩ := a
        obtain ⟨val_1, property_1⟩ := x
        simp_all only [Subtype.mk.injEq]
        simp_all only [↓reduceDIte]

    case neg =>
      dsimp [classOf] at h
      simp only [Finset.mem_filter] at h
      simp at h
      simp
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := a
      simp_all only [Subtype.mk.injEq]
      split
      next h_1 =>
        subst h_1
        simp_all only [Subtype.coe_eta]
        contrapose! h
        simp_all only [ne_eq]
        rfl
      next h_1 =>
        simp_all only
        rfl

lemma OldNew_id (s : Setup_spo α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2)
  (Cls : Quotient (restrictedSetoid s x)) :
  toNew s x hx (toOld s x Cls) = Cls :=
by
  induction Cls using Quotient.inductionOn
  case h a =>
    dsimp [toNew]
    dsimp [toOld]
    dsimp [toErased]
    dsimp [representativeNeSelf]
    have: a.val ≠ x.val := by --暗黙に使っている。
      dsimp [representativeNeSelf]
      obtain ⟨val_1, property_1⟩ := a
      simp_all only [Subtype.mk.injEq]
      simp_all only [ge_iff_le, mem_erase, ne_eq, not_false_eq_true]
    simp_all only [ne_eq, Subtype.coe_eta, dite_eq_ite, Quotient.eq]
    obtain ⟨val, property⟩ := x
    simp_all only [Subtype.mk.injEq, ↓reduceIte]
    simp_all only [ge_iff_le]
    rfl


--toNewやtoOldで順序が保存されることを示す必要があるのか。そのためには、新しい同値類の構造で順序が導入されている必要があるが。
--段階的に導入するのがいいのか。そのためには、setup_spoになることをまず証明するか。
--fqまでで、まだloopも定義されていない。setup_spo0みたいなものを作った方がいいかも。



noncomputable def setup_trace_base (s : Setup_spo α)(x: s.V) (hx:(classOf s (@Quotient.mk _ s.setoid x
)).card ≥ 2): Setup_spo_base α :=
{
  V := s.V.erase x,
  nonemp := by
    have : (classOf s (@Quotient.mk _ s.setoid x)).card > 1 := by
      exact hx
    have : ∃ x0, x0 ∈ classOf s (@Quotient.mk _ s.setoid x) ∧ x0 ≠ x := by
      exact exists_ne_of_one_lt_card hx x
    simp_all only [ge_iff_le, gt_iff_lt, ne_eq, Subtype.exists, coe_mem, erase_nonempty, nontrivial_coe]
    obtain ⟨val, property⟩ := x
    obtain ⟨w, h⟩ := this
    obtain ⟨w_1, h⟩ := h
    obtain ⟨left, right⟩ := h
    simp_all only [Subtype.mk.injEq]
    constructor
    · simp_all only [mem_coe, ne_eq]
      apply And.intro
      · apply w_1
      · use val

  setoid := restrictedSetoid s x

  fq := fun q => toNew s x hx (s.fq (toOld s x q))
}

--(setup2_trace s x).fqをn回適用したもの(setup2_trace s x).fq^[n]は、
--(toNew s x hx (s.fq^[n] (toOld s x q))と等しい。
--使うかどうか不明。
lemma setup2_trace_fq_one (s : Setup_spo α) (x: s.V) (hx:(classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2) :
  (setup_trace_base s x hx).fq = fun q => toNew s x hx (s.fq (toOld s x q)) := by
  dsimp [setup_trace_base]

lemma setup2_trace_fq_n (s : Setup_spo α) (x: s.V) (hx:(classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2) (n :Nat):
  ((setup_trace_base s x hx).fq)^[n] = fun q => toNew s x hx (s.fq^[n] (toOld s x q)) := by
  dsimp [setup_trace_base]
  induction n
  case zero =>
    simp_all only [Function.iterate_zero, id_eq]
    let no := OldNew_id s x hx
    simp_all only [no]
    obtain ⟨val, property⟩ := x
    simp_all only
    rfl

  case succ n ih =>
    simp_all only [Function.iterate_succ, ih]
    simp
    rw [←ih]
    funext q
    dsimp [setup_trace_base]
    let no := NewOld_id s x hx
    simp_all only [no]

/-
  noLoop := by
    intro q1 q2 hxy hyx
    dsimp [restrictedSetoid] at *
    obtain ⟨x, hx⟩ := Quotient.exists_rep q1
    obtain ⟨y, hy⟩ := Quotient.exists_rep q2
    --新しいところにループがあると、古いところにもループができてしまう。
    sorry
  spo := sorry
  h_spo := by
    dsimp [partialOrderOfFq]
    dsimp [reach]
    sorry
  singleton_if_not_maximal := by
    intro q hq
    dsimp [isMaximal_spo] at hq
    obtain ⟨x, hx⟩ := Quotient.exists_rep q
    sorry
-/
