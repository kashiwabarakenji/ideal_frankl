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

--Setup_spo2から得られるideal全体の集合族において、同値類の大きさが2以上のときに、1元traceしても、またSetup2になる。
--同値類の要素は、パラレルであることは事前に示した方がいいのか。

def restrictedSetoid (s: Setup_spo2 α)(x : {x : α // x ∈ s.V}): Setoid {y : α // y ∈ s.V.erase x.val} :=
  Setoid.comap
    (fun y => ⟨y.val, Finset.mem_of_mem_erase y.property⟩)
    s.setoid

--新旧の同値類同士は全単射するので、fqを定義するには、それの対応の写像を作る必要がある。
def toOld (s : Setup_spo2 α) (x : {x : α // x ∈ s.V})
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
  (s : Setup_spo2 α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s.toSetup_spo ⟦x⟧).card ≥ 2) :
    { y // y ∈ s.V.erase ↑x } :=
  have h' : ∃ b ∈ classOf s.toSetup_spo ⟦x⟧, b ≠ x := exists_ne_of_one_lt_card hx x
  let b := Classical.choose (exists_ne_of_one_lt_card hx x)
  have hb := Classical.choose_spec (exists_ne_of_one_lt_card hx x)
  ⟨b, by
    simp only [Finset.mem_erase]
    exact ⟨Subtype.coe_ne_coe.mpr hb.right, b.property⟩⟩

lemma representativeNeSelf_mem_classOf
  (s : Setup_spo2 α) (x : {x // x ∈ s.V}) (hx : 2 ≤ (classOf s.toSetup_spo ⟦x⟧).card) :
  ⟨(representativeNeSelf s x hx).val, Finset.mem_of_mem_erase (representativeNeSelf s x hx).property⟩ ∈ (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).erase x :=
by
  dsimp [representativeNeSelf]
  have hb := Classical.choose_spec (exists_ne_of_one_lt_card hx x)
  simp_all only [ne_eq, Subtype.coe_eta, mem_erase, not_false_eq_true, and_self]

--入っている値の範囲を変えたくて、使わなくなった。
noncomputable def representativeNeSelf.old
  (s : Setup_spo2 α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s.toSetup_spo ⟦x⟧).card ≥ 2) :
    (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).erase x :=

  have h' : ∃ b ∈ classOf s.toSetup_spo ⟦x⟧, b ≠ x := exists_ne_of_one_lt_card hx x
  let b := Classical.choose (exists_ne_of_one_lt_card hx x)
  have hb := Classical.choose_spec (exists_ne_of_one_lt_card hx x)
  ⟨b, by
    simp only [Finset.mem_erase]
    exact ⟨hb.right, hb.left⟩
  ⟩

noncomputable def toErased (s : Setup_spo2 α)
  (x : {x : α // x ∈ s.V})
  (hx : (classOf s.toSetup_spo ⟦x⟧).card ≥ 2) :
  { y // y ∈ s.V } → { y // y ∈ s.V.erase x } :=
  fun z =>
    if h : z = x then
      let z' := representativeNeSelf s x hx
      ⟨z'.val, by
        simp [Finset.mem_erase]
        --exact z'.val.property
        /-let zpr := z'.property
        dsimp [classOf] at zpr
        rw [Finset.mem_erase] at zpr
        rw [Finset.mem_filter] at zpr
        simp at zpr
        convert zpr.1
        simp_all only [iff_false, z']
        obtain ⟨left, right⟩ := zpr
        intro a
        exact left (Subtype.ext a)
        -/
      ⟩
    else
      ⟨z.val, by
        simp [Finset.mem_erase, h]
        exact Subtype.coe_ne_coe.mpr h⟩

lemma toErased_eq_ne
  (s : Setup_spo2 α) (x z : {x // x ∈ s.V})
  (hx : 2 ≤ (classOf s.toSetup_spo ⟦x⟧).card)
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

noncomputable def toNew (s : Setup_spo2 α) (x : {x : α // x ∈ s.V})
  (hx : (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2)
  : Quotient s.setoid → Quotient (restrictedSetoid s x) :=
  fun oldCls =>
    @Quotient.liftOn {x // x ∈ s.V} (Quotient (restrictedSetoid s x)) s.setoid oldCls

  (fun z => @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx z))

  (by
    intros a b hab
    dsimp only [toErased]

    split
    · split
      · -- case a = x, b = x
        apply Quotient.sound
        rename_i h h_1
        subst h h_1
        simp_all only [Setoid.refl]
      · let rsp := (representativeNeSelf s x hx).property
        let rmc := representativeNeSelf_mem_classOf s x hx
        have : @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx a) =
            @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx b) := by
          dsimp [toErased]
          dsimp [restrictedSetoid]
          simp
          rename_i h_1
          simp only [h_1]
          split_ifs with h_2
          rename_i h
          subst h
          simp_all only
          --dsimp [Setoid.comap]
          --dsimp [representativeNeSelf]


          rename_i h
          --subst h
          --simp_all only [mem_erase, ne_eq, not_false_eq_true, true_and]

          rename_i h_3
          --subst h_3
          simp_all only [mem_erase, ne_eq, not_false_eq_true, true_and, coe_mem, and_true]
        -- case a = x, b ≠ x
          have :b ∈ (classOf s.toSetup_spo ⟦x⟧).erase x :=
          by
            dsimp [classOf]
            rw [Finset.mem_erase]
            constructor
            ·
              rename_i h
              --subst h
              simp_all only [not_false_eq_true, ne_eq]
            · rw [Finset.mem_filter]
              constructor
              ·
                rename_i h
                --subst h
                simp_all only [not_false_eq_true, mem_attach]
              ·
                rename_i h
                --subst h
                simp_all only [not_false_eq_true, Quotient.eq]
                obtain ⟨val, property⟩ := a
                obtain ⟨val_1, property_1⟩ := b
                --simp_all only [Subtype.mk.injEq]
                symm
                exact hab
          have : ↑b ∈ s.V.erase ↑x := by
            rename_i h
            subst h
            simp_all only [not_false_eq_true, mem_erase, ne_eq, true_and, coe_mem, and_true]
            obtain ⟨val, property⟩ := a
            obtain ⟨val_1, property_1⟩ := b
            simp_all only [Subtype.mk.injEq, not_false_eq_true]
        have rrr:(restrictedSetoid s x).r (representativeNeSelf s x hx) ⟨↑b,  this⟩ :=
          by
            dsimp [restrictedSetoid]
            dsimp [Setoid.comap]
            dsimp [representativeNeSelf]
            sorry
        apply Quotient.sound

        apply (restrictedSetoid s x).trans
        · apply s.setoid.refl
        · subst_vars
          dsimp [representativeNeSelf]
          --dsimp [Classical.choose]
          dsimp [classOf]
          rename_i h_3 this_1
          exact rrr


    · split
      · -- case a ≠ x, b = x
        apply Quotient.sound
        apply (restrictedSetoid s x).trans
        · apply s.setoid.refl
        · let rsp := (representativeNeSelf s x hx).property
          have :a ∈ (classOf s.toSetup_spo ⟦x⟧).erase x :=
          by
            rename_i h_1
            subst h_1
            simp_all only [mem_erase, ne_eq, not_false_eq_true, true_and]
            obtain ⟨val, property⟩ := a
            obtain ⟨val_1, property_1⟩ := b
            simp_all only [Subtype.mk.injEq]
            dsimp [classOf]
            simp_all only [Quotient.eq, mem_filter, mem_attach, true_and]
            exact hab
          --aとxは、同じ同値類に入っている。暗黙に後ろで使っている。
          have : @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx a)
            = @Quotient.mk _ (restrictedSetoid s x) (toErased s x hx x) :=
          by
            dsimp [toErased]
            simp
            dsimp [restrictedSetoid]
            rename_i h_1
            split_ifs with h_1
            rename_i h
            simp_all only
            exact?


          --#check (representativeNeSelf s x hx).property
          have : (restrictedSetoid s x).r (toErased s x hx a) (toErased s x hx x) :=
          by
            rename_i h_1 this_1
            subst h_1
            simp_all only [mem_erase, ne_eq, not_false_eq_true, true_and, Quotient.eq]

          rename_i h_1 h_2 h_3 h_4
          have ha_ne_x : a ≠ x := h_1
          have h₁ : toErased s x hx a = ⟨a.val, by
          simp [Finset.mem_erase]
          exact Subtype.coe_ne_coe.mpr ha_ne_x⟩ := toErased_eq_ne s x a hx ha_ne_x

          have h₂ : (toErased s x hx x).val = (representativeNeSelf s x hx).val:= by
            dsimp [toErased]
            simp only [dif_pos rfl]
            subst h_2
            simp_all only [not_false_eq_true, mem_erase, ne_eq, true_and, Quotient.eq, ↓reduceDIte]

          rw [←h₁]

          have h_eq : toErased s x hx x =
            ⟨↑↑(representativeNeSelf s x hx), (representativeNeSelf s x hx).property⟩ :=
              Subtype.ext h₂
          subst h_2
          simp_all only [not_false_eq_true, mem_erase, ne_eq, true_and, Subtype.coe_eta, Quotient.eq]
          obtain ⟨val, property⟩ := a
          obtain ⟨val_1, property_1⟩ := b
          simp_all only
          exact h_4

      · -- case a ≠ x, b ≠ x
        apply Quotient.sound
        exact hab
  )

  /-
  (fun z => --fを構成する。
    if h : z = x then  --zがxに一致する場合は、xの同値類の要素を取る。
      --let eno := exists_ne_of_one_lt_card hx z
      let x0 := representativeNeSelf s x hx  -- x0 : (classOf s.toSetup_spo ⟦x⟧).erase x
      @Quotient.mk _ (restrictedSetoid s x) ⟨x0.val, by
        simp [Finset.mem_erase, h]
        let x0p := x0.property
        dsimp [classOf] at x0p
        rw [Finset.mem_erase] at x0p
        convert x0p.1.symm
        subst h
        simp_all only [ne_eq, Quotient.eq, mem_filter, mem_attach, true_and, x0]
        apply Iff.intro
        · intro a
          rw [Subtype.ext_iff, a]
        · intro a
          simp_all only [not_true_eq_false]
      ⟩
      -/
      /-
      let x0 := Classical.choose (exists_ne_of_one_lt_card hx z)
      have ha := Classical.choose_spec (exists_ne_of_one_lt_card hx z)
      let ha_inClass := ha.left --zとxは同じ同値類。
      let ha_ne := ha.right
      @Quotient.mk _ (restrictedSetoid s x) ⟨x0.val, by
        simp [Finset.mem_erase, h]
        apply Subtype.coe_ne_coe.mpr
        subst h
        simp_all only [ne_eq, not_false_eq_true, x0]
      ⟩
      -/
    else
      @Quotient.mk _ (restrictedSetoid s x) ⟨z.val, by
        simp [Finset.mem_erase, h]
        exact Subtype.coe_ne_coe.mpr h
      ⟩
  )
  (by
    intros a b hab
    simp
    split
    · split-- case: a = x, b = x
      · apply Quotient.sound
        rename_i h h_1
        subst h_1 h
        simp_all only [Setoid.refl]
      · -- case: a = x, b ≠ x
        apply Quotient.sound
        let rsp := (representativeNeSelf s x hx).property
        have : b.val ∈ s.V.erase x.val := by
          simp [Finset.mem_erase]
          rename_i h h_1
          subst h
          obtain ⟨val, property⟩ := a
          obtain ⟨val_1, property_1⟩ := b
          simp_all only [Subtype.mk.injEq, not_false_eq_true]
        have : b ∈ classOf s.toSetup_spo (@Quotient.mk _ s.setoid x) := by
          obtain ⟨val, property⟩ := a
          obtain ⟨val_1, property_1⟩ := b
          simp_all only [Subtype.mk.injEq]
          dsimp [classOf]
          rw [Finset.mem_filter]
          constructor
          ·
            rename_i h h_1
            subst h
            simp_all only [Subtype.mk.injEq, mem_erase, ne_eq, not_false_eq_true, and_self, mem_attach]
          · exact Quotient.sound (id (s.setoid.symm hab))
        dsimp [representativeNeSelf]
        dsimp [classOf] at this
        rw [Finset.mem_filter] at this
        -- b ∈ classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)
        --から、⟨↑(Classical.choose ⋯), ⋯⟩ ≈ ⟨↑b, ⋯⟩
        --をいう必要あり。
        --両方ともQuotient.mkで等しい。
        have : @Quotient.mk _ (restrictedSetoid s x) x = @Quotient.mk _ (restrictedSetoid s x) b :=

          by
          simp [Finset.mem_erase]
          subst h
          simp_all only [ne_eq, Quotient.eq, mem_filter, mem_attach, true_and, x0]



        exact hab.symm
        /-
        apply (restrictedSetoid s x).trans
        · sorry
        · apply (restrictedSetoid s x).refl
        -/
    · -- case: a ≠ x, b = x
      split
      · apply Quotient.sound
        rename_i h h_1
        sorry
      · -- case: a ≠ x, b ≠ x
        apply Quotient.sound
        exact hab
  )
/-
    split
    · split
      · simp_all only [Setoid.refl]
      · -- もともとの setoid で a ≈ b なので、restrictedSetoid でも同値
        apply Quotient.sound
        rename_i h_1 h_2
        let x0 := Classical.choose (exists_ne_of_one_lt_card hx x)
        let rr := (restrictedSetoid s x).refl
        have ha := Classical.choose_spec (exists_ne_of_one_lt_card hx x)
        --show ⟨↑(Classical.choose ⋯), ⋯⟩ ≈ ⟨↑b, ⋯⟩
        apply (restrictedSetoid s x).trans
        · sorry
        · sorry
        · subst h_1
          simp_all only [ne_eq, mem_erase]
          obtain ⟨val, property⟩ := a
          obtain ⟨val_1, property_1⟩ := b
          obtain ⟨val_2, property_2⟩ := x0
          obtain ⟨left, right⟩ := ha
          simp_all only [Subtype.mk.injEq]
          tauto
    · -- restrictedSetoid で同値 ⇒ もともとの setoid でも同値
      split
      · rename_i h1 h2
        apply Quotient.sound


        -- ここで必要な証明を行う
        sorry
      ·
        simp_all only [ge_iff_le, Quotient.eq]
        obtain ⟨val, property⟩ := x
        obtain ⟨val_1, property_1⟩ := a
        obtain ⟨val_2, property_2⟩ := b
        simp_all only
        exact hab
  )
-/
/-  --Quotient.liftOn.{u, v} {α : Sort u} {β : Sort v} {s : Setoid α} (q : Quotient s) (f : α → β)  (c : ∀ (a b : α), a ≈ b → f a = f b) : β
  · intro z

    have h : (z = x) ∨ (z ≠ x) := by
      simp_all only [ge_iff_le, ne_eq]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := z
      simp_all only [Subtype.mk.injEq]
      tauto
    cases h with
    | inl heq =>
      let ⟨a, ⟨ha_inClass, ha_ne⟩⟩ := exists_ne_of_one_lt_card hx z
      let qm := @Quotient.mk _ (restrictedSetoid s x) --⟨a.val, by simp [Finset.mem_erase, ha_ne]⟩

      intro b
      intro hh
      -- b.val が s.V.erase x.val に入っていることを示すための証明ブロック
      have hb : b.val ∈ s.V.erase x.val := by
        simp [Finset.mem_erase]
        subst  heq
        simp_all only [ne_eq, Subtype.mk.injEq]
        sorry
        --exact ⟨ne.symm ha_ne, b.property⟩

      -- b を restrictedSetoid の要素として mk
      have qb : Quotient (restrictedSetoid s x) :=
        qm ⟨b.val, hb⟩

      -- 目標は qm ⟨a.val, ...⟩ = qb
      apply Quotient.sound
      -- もとの setoid で a ≈ b なので、restrictedSetoid でも同値
      sorry
      --apply hh.trans
      --apply (Setoid.symm (Setoid.refl _))



    | inr hne =>
      intro b hh
      apply congrFun rfl


-/

/-

λ oldCls =>
  Quotient.liftOn oldCls
  (by
    intro z
    by_cases h : z = x
    · -- z = x のとき（クラス [x] の処理）
      have eno := exists_ne_of_one_lt_card hx z
      match eno with
      | ⟨a, ⟨ha_inClass, ha_ne⟩⟩ =>
        exact @Quotient.mk _ (restrictedSetoid s x) ⟨a.val, by
          simp [Finset.mem_erase]
          subst h
          simp_all only [ne_eq, Subtype.mk.injEq]
        ⟩
    · -- z ≠ x のとき（そのまま使える）
      exact @Quotient.mk _ (restrictedSetoid s x) ⟨z.val, by
        simp [Finset.mem_erase, h]
        exact Subtype.coe_ne_coe.mpr h
      ⟩
  )
  (by
    -- Quotient.lift の well-definedness の証明
    intros a b hab
    exact Eq.propIntro (fun a => a) fun a => a
  )
-/

/-
    (fun (z : {z : α // z ∈ s.V}) =>
      if h : z = x then
        -- クラス [x] の場合：
        -- x と同じクラスの中で x ≠ a なる a を一つ取って，新しい代表にする
        by
          let eno := exists_ne_of_one_lt_card hx z  -- クラスの要素が2以上あるので取り出せる
          obtain ⟨a, ha_inClass, ha_ne⟩ := eno
          exact Quotient.mk ⟨a.val, by
          simp [Finset.mem_erase]
          subst h
          simp_all only [ne_eq, Subtype.mk.injEq]
          ⟩

      else
        -- クラス [z] で z ≠ x の場合：
        -- そのまま z を新しい台集合の要素として使える
        @Quotient.mk _ (restrictedSetoid s x) (⟨z.val, by
          simp [h]; exact Subtype.coe_ne_coe.mpr h--exact z.property
        ⟩ : {y // y ∈ s.V.erase x.val})
    )
    (by
      intros a b hab
      apply Quotient.sound
      -- 「元の setoid で同値 ⇒ restrictedSetoid でも同値」が成り立つ
      exact hab
    )
    -/

def setup2_trace (s : Setup_spo2 α)(x: s.V) (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x
)).card ≥ 2): Setup_spo2 α :=


{
  V := s.V.erase x,
  nonemp := by
    have : (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card > 1 := by
      exact hx
    have : ∃ x0, x0 ∈ classOf s.toSetup_spo (@Quotient.mk _ s.setoid x) ∧ x0 ≠ x := by
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

  fq := fun q => Quotient.map (fun y => ⟨y.val, Finset.mem_of_mem_erase y.property⟩) s.fq
    (by
      intro a b h
      dsimp [restrictedSetoid] at *
      obtain ⟨x, hx⟩ := Quotient.exists_rep a
      obtain ⟨y, hy⟩ := Quotient.exists_rep b
      subst hx
      subst hy
      exact h)

  noLoop := by
    intro q1 q2 hxy hyx
    dsimp [restrictedSetoid] at *
    obtain ⟨x, hx⟩ := Quotient.exists_rep q1
    obtain ⟨y, hy⟩ := Quotient.exists_rep q2
    have : x.val ≠ y.val := by

      intro h
      subst h
      exact hx.2 (Finset.mem_erase.2 ⟨hx.1, hy.1⟩)
    have : s.spo.le x y = reach (fq s) x y := by
      dsimp [reach]
      rw [spole_iff_po]
      exact hxy
    have : s.spo.le y x = reach (fq s) y x := by
      dsimp [reach]
      rw [spole_iff_po]
      exact hyx
    apply s.spo.le_antisymm
    · subst this
      exact hxy
    · subst this
      exact hyx
}
