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
import rooted.functionalTreePreorder
import rooted.functionalTreePartialorder

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

--このファイルは、Setup_spoのうち、traceに入る前の部分の話。

--fqまで定義すれば同値類上の前順序が定まる。fのループが許されているので仮定としては弱い。loopがないことまで証明して半順序。
structure Setup_spo_base (α : Type) [Fintype α] [DecidableEq α] where
  (V : Finset α)
  (nonemp   : V.Nonempty)
  (setoid : Setoid {x : α // x ∈ V})
  (fq : Quotient setoid → Quotient setoid)

--半順序に関することなので、commonから移動してきた。Setup_spoの定義で使用するもの。
--でも3つの外ファイルから参照されている。
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

--ここでのfqはSetup_spo_baseのfq。
structure Setup_spo (α : Type) [Fintype α] [DecidableEq α] extends Setup_spo_base α where
  -- antisymmetry を保証する仮定：ループがあれば自明なもののみ
  --仮定としては、Setup_spoよりも弱く、normalized degree sumが非正とはいえない。
  (noLoop : ∀ x y : Quotient setoid,
    (reach fq x y → reach fq y x → x = y))
  (spo : PartialOrder (Quotient setoid))
  (h_spo : spo = partialOrderOfFq fq noLoop)
-- spoとh_spoは、ここにいれないで、def spo : PartialOrder _ := partialOrderOfFq fq noLoopとしたほうがいい。

def isMaximal_spo (s: Setup_spo α) (x : Quotient s.setoid) : Prop :=
  ∀ y : Quotient s.setoid,
  s.spo.le x y → s.spo.le y x

----Setup_spoの枠組みにおける同値類に関すること。

--Quotientに対するそれに属する。頂点の集合。
--eqClassの定義と同じなので必要なかったかも。そっちは、Setup2用。setoidを引数にすれば統一できた。
def classOf (s : Setup_spo α) (q : Quotient s.setoid) [DecidableEq (Quotient s.setoid)]  : Finset {x // x ∈ s.V} :=
  Finset.filter (fun (a : {x // x ∈ s.V}) => @Quotient.mk'' _ s.setoid a = q) s.V.attach
--以下とほぼ同じ
--noncomputable def eqClass_setup (s: Setup α) (x : {x : α // x ∈ s.V}) : Finset {x // x ∈ s.V} :=
--  s.V.attach.filter (fun y => s.setoid.r x y)
--noncomputable def classOf'
--    {α : Type} {V : Finset α} (std : Setoid {x // x ∈ V})
--    (q : Quotient std) : Finset {x // x ∈ V} :=
--  V.attach.filter (fun a => @Quotient.mk _ std a = q)
-- def classOf (s : Setup_spo α) := classOf' s.setoid
-- とまとめられるとのアドバイス。


--ためしにsetoidに対して定義してみた。このほうがいいともいえないかも。
noncomputable def classOfsetoid (V: Finset α) (std: Setoid {x : α // x ∈ V}) (x : {x : α // x ∈ V}) :
  Finset {x : α // x ∈ V} :=
  Finset.filter (fun (a : {x : α // x ∈ V}) => std.r x a) V.attach

--要素にひとつに対するそれと同値な頂点全体がclassOf。引数がs.Vの点。
noncomputable def classOfx (s : Setup_spo α) (x : {x : α // x ∈ s.V}) :
  Finset {x : α // x ∈ s.V} :=
  classOf s (@Quotient.mk _ s.setoid x)
--classOf s ⟦x⟧で十分ではないかということ。そのように変更したらクラスでエラー。

--同値類が非空であること。
lemma classOf_nonempty (s : Setup_spo α) (q : Quotient s.setoid) :
  (classOf s q).Nonempty := by
  dsimp [classOf]
  rw [Finset.filter_nonempty_iff]
  let a := Quotient.out q
  use a
  constructor
  · exact mem_attach s.V a
  · exact Quotient.out_eq q

--わざわざ定義するまでもないかも。頂点集合に対して、それに対応するQuotientの集合。
--何ヶ所かで使っている。
noncomputable def QuotientOf (s: Setup_spo α) (xx : Finset {x : α // x ∈ s.V}) :
  Finset (Quotient s.setoid) :=
  xx.image (@Quotient.mk _ s.setoid)

--setoidで同値なことと、classOfの関係。TraceIdealからも利用されている。
--trace に直接関係がないので、SPOなどに移動した。上の定理とかぶってないか。
lemma classOf_setoid
  (s : Setup_spo α) (y z: {x : α // x ∈ s.V}) :
  s.setoid.r y z ↔ y ∈ (classOf s ⟦z⟧)  :=
by
  apply Iff.intro
  · intro h
    dsimp [classOf]
    rw [Finset.mem_filter]
    constructor
    · simp_all only [mem_attach]
    · dsimp [classOf]
      simp_all only [Quotient.eq]
  · intro h
    dsimp [classOf] at h
    rw [Finset.mem_filter] at h
    simp_all only [mem_attach, Quotient.eq, true_and]

--classOfで同じことと、setoidで同じことの関係。
--上の補題と、定義から自明かもしれないが。下で使っている。
--これもtraceに関係がない。
lemma classOf_quotient
  (s : Setup_spo α) (y : {x : α // x ∈ s.V}) (q:Quotient s.setoid) :
  q = @Quotient.mk' _ s.setoid y ↔ y ∈ (classOf s q) := by
  dsimp [classOf]
  rw [Finset.mem_filter]
  constructor
  ·
    intro a
    subst a
    simp_all only [mem_attach, true_and]
    obtain ⟨val, property⟩ := y
    rfl
  · dsimp [classOf]
    intro h
    symm
    exact h.2

--自分自身も、同値類に入る。外から使う。
--traceに関係がない。
lemma classOf_self
  (s : Setup_spo α) (x : {x : α // x ∈ s.V}) :
  x ∈ (classOf s ⟦x⟧) := by
  dsimp [classOf]
  rw [Finset.mem_filter]
  constructor
  · exact mem_attach s.V x
  · dsimp [classOf]

--setup_spoの枠組みに関するreachに関すること。

lemma reach_leq (s : Setup_spo α) (q1 q2 : Quotient s.setoid) :
  reach s.fq q1 q2 → s.spo.le q1 q2 := by
  --これはs.spo.leの定義な気もするが。
  intro h
  rw [s.h_spo]
  dsimp [partialOrderOfFq] at *
  exact h

--すぐ下で使っている。外でも使っている。
lemma reach_leq_rev (s : Setup_spo α) (q1 q2 : Quotient s.setoid) :
  s.spo.le q1 q2 →  reach s.fq q1 q2  := by
  intro h
  rw [s.h_spo] at h
  dsimp [partialOrderOfFq] at h
  dsimp [reach]
  exact h



/-
--fq_lemmaと内容が被っている。こっちは、reachで書き換えたもの。使ってないのかも。使ってもよい。
lemma reach_po_leq_rev (s : Setup2 α) (q1 q2 : Quotient s.setoid) :
  s.po.le q1 q2 → reach (fq s) q1 q2 :=
by
  --rw [s.h_po]これをするとfq_lemmaに適用できない。
  dsimp [reach]
  intro h
  let fql := fq_lemma s q1 q2 h
  obtain ⟨n, hn⟩ := fql
  use n
  exact hn.symm
-/

-- 証明すべきこと
--1. setup2から得られるsetoidとpartialOrderは、Setup_spo2の定義を満たす。
--2. Setup_spo2から得られるideal全体の集合族において、極大の同値類の大きさが2以上のときに、1元traceしても、またSetup2になる。
--3. Setup_spo2から得られるideal全体の集合族において、極大元の同値類に属する要素は、rareである。
--4. 閉集合族において、パラレルな要素を持つrareな要素のtraceは、標準化次数和を上げる。
--5. Setup2から得られる集合族の極大元に対応する同値類の大きさがすべて1であるときは、idealの集合族は、台集合上の半順序(setup_po)のideal集合族に一致する。

--Setup2に対する対応するSetup_spoの要素。のちにSetup_spo2に拡張される。それがsetup2_induces_spo。
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
      have : q1 ≤ q2 := reach_po_leq s q1 q2 hxy
      have : q2 ≤ q1 := reach_po_leq s q2 q1 hyx
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
        let rl := reach_po_leq s x y hxy
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
        let rl := reach_po_leq s y x hyx
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

--eqClassとclassOfは同じもの。classOfは、setup_spoから定義されるところが違う。
--統合可能。
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

--noncomputable def eqClass_setup
--    (t : Setup α) (x : {x : α // x ∈ t.V}) :
--    Finset {x // x ∈ t.V} :=
--  classOf' t.V t.setoid ⟦x⟧
--のように統合できる。

--上とほぼ同じだが、qを与えたもの。
lemma eqClass_Class_of2 (s: Setup2 α) (q : Quotient s.setoid) :
  eqClass_setup s.toSetup (Quotient.out q) = (classOf (setup_setupspo s) q) :=
by
  rw [eqClass_Class_of]
  congr
  simp [Quotient.mk']

--Setup2の順序がspoの順序に拡張できること。これも上の定理に統合できる。
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

/-
--わざわざ定理にする必要はなくて、Quotient.eqとおなじだった。でもTraceIdeal2などで使っている。なくした。
lemma setroid_quotient (s: Setup_spo α) (y z: {x : α // x ∈ s.V}) :
  (@Quotient.mk _ s.setoid y) = (@Quotient.mk _ s.setoid z)
  ↔ s.setoid.r y z := by
  simp_all only [Quotient.eq]
-/
