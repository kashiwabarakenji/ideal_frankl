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

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]


--前順序が同値類を作り、それ上の半順序を作るという一般的な話の部分。setoidが導入されている。
def equiv_rel {α : Type} [Preorder α] (x y : α) : Prop := x ≤ y ∧ y ≤ x

lemma equiv_rel_refl {α : Type} [Preorder α]  : Reflexive (@equiv_rel α _) := fun x => ⟨le_refl x, le_refl x⟩

lemma equiv_rel_symm  {α : Type} [Preorder α] : Symmetric (@equiv_rel α _) :=
  fun (x y : α) (h : equiv_rel x y) => ⟨h.2, h.1⟩

lemma equiv_rel_trans {α : Type} [Preorder α] : Transitive (@equiv_rel α _) :=
  fun x y z ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨le_trans h1 h3, le_trans h4 h2⟩

lemma equiv_rel_equiv {α : Type}  [Preorder α]: Equivalence (@equiv_rel α _) :=
  ⟨equiv_rel_refl, @equiv_rel_symm α _, @equiv_rel_trans α _⟩

instance setoid_preorder {α : Type}[Preorder α]: Setoid α := ⟨@equiv_rel α _, equiv_rel_equiv⟩

--消すとエラー。[∀ a b : α, Decidable (a ≤ b)]も必要。
noncomputable instance decidableEq_Quotient_setoid_preorder {α : Type} [Preorder α] [∀ a b : α, Decidable (a ≤ b)] :
  DecidableEq (Quotient (setoid_preorder : Setoid α)) :=
by
  infer_instance

--noncomputable instance preorder_Quotient_setoid_preorder {α : Type} [Preorder α] : Preorder (Quotient (setoid_preorder : Setoid α)) :=

noncomputable instance finite_quotient_classes {α : Type} [Preorder α] [Fintype α]: Finset (Quotient (@setoid_preorder α _)) :=
  Finset.image (@Quotient.mk α setoid_preorder) (Finset.univ:Finset α)

example [Preorder α]: Nonempty (Finset (Quotient (@setoid_preorder α _))) :=
  ⟨finite_quotient_classes⟩

instance quotient_partial_order {α : Type}[Preorder α]: PartialOrder (Quotient (@setoid_preorder α _)) where
  le := Quotient.lift₂ (fun x y => x ≤ y) (fun a b c d ⟨hab1, hab2⟩ ⟨hcd1, hcd2⟩ =>
    propext ⟨fun h => le_trans hab2 (le_trans h hcd1),
    by
      intro a_1
      --hab1 : a ≤ cと、a_1 : c ≤ dと、hcd2 : d ≤ bからa ≤ bがいえる。
      exact le_implies_le_of_le_of_le hab1 hcd2 a_1
    ⟩)
  le_refl := fun x => Quotient.inductionOn x (fun a => le_refl a)
  le_trans := fun x y z => Quotient.inductionOn₃ x y z (fun a b c => le_trans)
  le_antisymm := fun x y => Quotient.inductionOn₂ x y (fun a b h1 h2 => Quotient.sound ⟨h1, h2⟩)

--前順序の大小をsetoid上の半順序に持ち上げ。
lemma quotient_le_iff {α : Type}[Preorder α] (a b : α) :
  (quotient_partial_order.le (Quotient.mk setoid_preorder a : Quotient (@setoid_preorder α _))  (Quotient.mk setoid_preorder b)) ↔ a ≤ b := by
  rfl  -- quotient_partial_order での定義を見ると、ちょうどこの形になります

--前順序の要素を対応する同値類に移す。
noncomputable def pullback {α : Type} [Fintype α] [Preorder α]
  (J : Finset (Quotient (@setoid_preorder α _))) : Finset α :=
  { a : α | Quotient.mk setoid_preorder a ∈ J }

def isMaximal [Preorder α] (a : α) : Prop :=
  ∀ b : α, a ≤ b → b ≤ a

/--
商集合上 `(Quotient setoid_preorder, ≤)` における「極大元」であることを表す述語です。
-/
def isMaximalQ [Preorder α](x : Quotient (@setoid_preorder α _)) : Prop :=
  ∀ y, x ≤ y → y ≤ x

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

structure IsIdeal {α : Type} [Fintype α] [Preorder α] (I : Finset α) : Prop where
  down_closed :
    ∀ {x}, x ∈ I → ∀ {y}, y ≤ x → y ∈ I
  directed :
    ∀ {x y}, x ∈ I → y ∈ I → ∃ z ∈ I, x ≤ z ∧ y ≤ z

/--
商集合 `(Quotient setoid_preorder, ≤)` における順序イデアル。
-/
structure IsIdealQ {α : Type} [Fintype α] [Preorder α]
  (J : Finset (Quotient (@setoid_preorder α _))) : Prop where
  down_closed :
    ∀ {x}, x ∈ J → ∀ {y}, y ≤ x → y ∈ J
  directed :
    ∀ {x y}, x ∈ J → y ∈ J → ∃ z ∈ J, x ≤ z ∧ y ≤ z

--Preorderのidealと、setoid上のidealの同値性を示す。
lemma IsIdealQ.pullback_isIdeal {α : Type} [Fintype α][Preorder α]
    {J : Finset (Quotient (@setoid_preorder α _))}
    (hJ : IsIdealQ J) :
    IsIdeal (pullback J) := by
  constructor
  · -- 下に閉じていることを示す
    -- x ∈ pullback J かつ y ≤ x のとき y ∈ pullback J を示す
    intro x hx y hyx
    -- hx: Quotient.mk x ∈ J, ここから下に閉じている性質を使う
    -- まず y ≤ x から (Quotient.mk y) ≤ (Quotient.mk x)
    have : (Quotient.mk setoid_preorder y : Quotient _) ≤ Quotient.mk setoid_preorder x := by
      rw [quotient_le_iff]
      exact hyx
    -- hJ.down_closed で J が商集合上で下に閉じているので
    -- Quotient.mk y も J に入る
    dsimp [pullback]
    simp
    have hhx: ⟦x⟧ ∈ J :=
    by
      dsimp [pullback] at hx
      simp_all only [mem_filter, Finset.mem_univ, true_and]
    exact hJ.down_closed hhx this
  · -- 有向性を示す
    intro x y hx hy
    -- x, y ∈ pullback J すなわち Quotient.mk x, Quotient.mk y が J に属する
    have hhx:  ⟦x⟧ ∈ J := by
      dsimp [pullback] at hx
      simp_all only [mem_filter, Finset.mem_univ, true_and]
    have hhy : ⟦y⟧ ∈ J := by
      dsimp [pullback] at hy
      simp_all only [mem_filter, Finset.mem_univ, true_and]
    obtain ⟨z, hzJ, hxz, hyz⟩ :=
      hJ.directed hhx hhy
    -- すると z ∈ J の代表元を w として、Quotient.mk w = z とすると w ∈ pullback J となる
    -- z はすでに (Quotient (@setoid_preorder α _)) 型の要素なので、代表元を取り出す
    rcases Quotient.exists_rep z with ⟨w, rfl⟩
    -- hxz : Quotient.mk x ≤ Quotient.mk w から x ≤ w へ
    rw [quotient_le_iff] at hxz hyz
    -- あとは w が pullback J に属することを示せば完了
    use w
    constructor
    · -- w ∈ pullback J を示す
      dsimp [pullback]
      simp
      exact hzJ
    · exact ⟨hxz, hyz⟩

noncomputable def pushforward {α : Type} [Fintype α] [Preorder α]
  (I : Finset α) : Finset (Quotient (@setoid_preorder α _)) :=
  Finset.univ.filter (fun q => ∃ a ∈ I, Quotient.mk setoid_preorder a = q)

/--
元の前順序でのイデアル I は、その同値類の集まり（pushforward I）も
商集合上のイデアルを成す。
-/
lemma IsIdeal.pushforward_isIdealQ {α : Type} [Fintype α] [Preorder α]
    {I : Finset α} (hI : IsIdeal I) :
    IsIdealQ (pushforward I) := by
  constructor
  · -- 下に閉じている
    intro x hx y hyx
    dsimp [pushforward] at hx
    rw [Finset.mem_filter] at hx
    rcases hx.2 with ⟨a, haI, rfl⟩
    rcases Quotient.exists_rep y with ⟨b, rfl⟩
    rw [quotient_le_iff] at hyx  -- b ≤ a
    -- I が下に閉じているので a ∈ I, b ≤ a ⇒ b ∈ I
    have hbI := hI.down_closed haI hyx
    dsimp [pushforward]
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ (⟦b⟧), ⟨b, hbI, rfl⟩⟩
  · -- 有向性
    intro x y hx hy
    dsimp [pushforward] at hx hy
    rw [Finset.mem_filter] at hx hy
    rcases hx.2 with ⟨a, haI, rfl⟩
    rcases hy.2 with ⟨b, hbI, rfl⟩
    -- I が有向 ⇒ ∃ c ∈ I, a ≤ c ∧ b ≤ c
    rcases hI.directed haI hbI with ⟨c, hcI, hac, hbc⟩
    use Quotient.mk setoid_preorder c
    constructor
    · dsimp [pushforward]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨c, hcI, rfl⟩⟩
    · rw [quotient_le_iff]
      rw [quotient_le_iff]
      exact ⟨hac, hbc⟩

--preorderとは限らないsetoidとそれ上のpartial orderが与えられた時に、それのidealとしてのSetFamilyの要素を定義する。
noncomputable def setoid_ideal_ClosureSystem {α : Type} [Fintype α] [DecidableEq α]  (V:Finset α) (nonemp: V.Nonempty)(r : Setoid { x // x ∈ V }) [PartialOrder (Quotient r)] : ClosureSystem α :=
{
    ground := V,
    sets := fun s =>
    ∃ (I : Finset (Quotient r)),
      (∀ q ∈ I, ∀ q', q' ≤ q → q' ∈ I) ∧  -- ideal 条件
      (s ⊆ V) ∧ ((hs:s⊆ V) → ∀ (x : α) (h : x ∈ s), Quotient.mk r ⟨x, by exact hs h⟩ ∈ I)
    inc_ground := by
      intro s a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      obtain ⟨left_1, right⟩ := right
      simp_all only [forall_true_left]
    nonempty_ground := by
      simp_all only
    has_ground := by --Vがsetsになることを示す。そのときは、すべての同値類がIに含まれる。
      simp_all only
      use Finset.univ
      constructor
      · simp_all
      · simp_all only [subset_refl, Finset.mem_univ, implies_true, imp_self, and_self]

    intersection_closed := by
      intro s t ⟨Ia, hIa, hsub_a, ha⟩ ⟨Ib, hIb, hsub_b, hb⟩
      let I := Ia ∩ Ib
      have hI : ∀ q ∈ I, ∀ q', q' ≤ q → q' ∈ I := by
        intro q hq q' hle
        simp only [Finset.mem_inter] at hq
        simp_all only [forall_true_left, Finset.mem_inter, I]
        simp_all only
        obtain ⟨left, right⟩ := hq
        apply And.intro
        · exact hIa q left q' hle
        · apply hIb
          on_goal 2 => {exact hle
          }
          · simp_all only
      use I
      constructor
      · exact hI
      constructor
      · simp_all only [forall_true_left, Finset.mem_inter, and_imp, I]
        simp_all only [I]
        exact inter_subset_left.trans hsub_a
      · intros x hx
        simp only [Finset.mem_inter]
        intro h
        simp_all only [forall_true_left, Finset.mem_inter, and_imp, and_self, I]
    /- こっちでも通る。どっちがよい。
    intersection_closed := by
      intro s t a b
      simp_all only --aもidealで、bもidealであるときに、a∩bもidealであることを示す。
      obtain ⟨Ia, hIa⟩ := a
      obtain ⟨Ib, hIb⟩ := b
      constructor
      · constructor
        · intro q hq q' hqq'
          obtain ⟨left, right⟩ := hIa
          obtain ⟨left_1, right_1⟩ := hIb
          apply left
          simpa
          simp_all only
        ·
          simp_all
          obtain ⟨left, right⟩ := hIa
          obtain ⟨left_1, right_1⟩ := hIb
          obtain ⟨left_2, right⟩ := right
          obtain ⟨left_3, right_1⟩ := right_1
          simp_all only [forall_true_left, implies_true, and_true]
          intro x hx
          simp_all only [Finset.mem_inter]
          obtain ⟨left_4, right_2⟩ := hx
          exact left_3 right_2
      -/

}


--noncomputable def preorder_ideal_system {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) [Preorder { x // x ∈ V }] (nonemp:V.Nonempty): ClosureSystem α :=

theorem Preorder_eq_PartialOrder {α : Type}  [Fintype α] [DecidableEq α]  (V : Finset α) (nonemp : V.Nonempty)[Fintype { x // x ∈ V }] [Preorder { x // x ∈ V }] :
  preorder_ideal_system V nonemp = setoid_ideal_ClosureSystem V nonemp (@setoid_preorder V _) := by
  --#check @setoid_ideal_ClosureSystem _ _ V nonemp (@setoid_preorder V _:Setoid V) _
  --#check setoid_ideal_ClosureSystem V nonemp (@setoid_preorder V _)
  ext
  · rfl
  · rename_i s
    dsimp [preorder_ideal_system, setoid_ideal_ClosureSystem]
    let st := (@setoid_preorder {x // x ∈ V} _)
    apply Iff.intro
    · intro a --sはpreorderのidealで、その性質がaに入っている。
      obtain ⟨hs, hhs⟩ := a --hsはsがVの要素であること。hhsは、sのidealとしての性質。
      --Iは同値類の集まりなので、sを含む同値類を全部持ってくるとよい。
      --I'は、sを含む同値類の全体。
      let I' := (Finset.univ : Finset V).filter (fun x =>
        ∀ a:V, st.r a x → a.val ∈ s) |>.image (Quotient.mk st)
      use I'
      --show (∀ q ∈ I', ∀ q' ≤ q, q' ∈ I') ∧ s ⊆ V ∧ ∀ (hs : s ⊆ V) (x : α) (h : x ∈ s), ⟦⟨x, ⋯⟩⟧ ∈ I'
      --示すべきことは、I'がidealになっていることと、sの要素の同値類が全部I'に入っていること。

      constructor
      · intro q hq q' hqq' --ここで使う性質は、I'の定義とhhs。qが大きい方で、q'が小さい方。q'がI'に入っていることを示すのが目標。
        dsimp [I'] at hq
        dsimp [I']
        rw [Finset.mem_image]
        rw [Finset.mem_image] at hq
        --obtain ⟨y, hy, rfl⟩ := hq --yはqの代表元。
        --rw [Finset.mem_filter] at ha
        --simp at hy
        --simp
        rcases Quotient.exists_rep q with ⟨y, hy⟩ --xはq'の代表元。
        rcases Quotient.exists_rep q' with ⟨x, hx⟩ --xはq'の代表元。
        use x
        simp
        constructor
        · intro aa bb
          intro h
          specialize hhs y
          have : y.val ∈ s :=
          by
            subst hy hx
            simp_all only [Subtype.forall, mem_filter, Finset.mem_univ, true_and, Quotient.eq, AntisymmRel.setoid_r,
              Subtype.exists, st, I']
            obtain ⟨val, property⟩ := y
            obtain ⟨val_1, property_1⟩ := x
            obtain ⟨w, h_1⟩ := hq
            obtain ⟨w_1, h_1⟩ := h_1
            obtain ⟨left, right⟩ := h_1
            simp_all only [st, I']
            apply left
            · exact right.symm
          specialize hhs this
          have : x ≤ y := by
            subst hy hx
            simp_all only [le_refl, Subtype.forall, coe_mem, mem_filter, Finset.mem_univ, true_and, Quotient.eq,
              AntisymmRel.setoid_r, Subtype.exists, st, I']
            obtain ⟨val, property⟩ := y
            obtain ⟨val_1, property_1⟩ := x
            obtain ⟨w, h_1⟩ := hq
            obtain ⟨w_1, h_1⟩ := h_1
            obtain ⟨left, right⟩ := h_1
            exact hqq'
          have : ⟨aa,bb⟩ ≤ y := by
            suffices  ⟨aa,bb⟩ ≤ x from by
              subst hy hx
              simp_all only [le_refl, Subtype.forall, coe_mem, mem_filter, Finset.mem_univ, true_and, Quotient.eq,
                AntisymmRel.setoid_r, Subtype.exists, ge_iff_le, st, I']
              apply Preorder.le_trans ⟨aa, bb⟩ x y this
              exact hqq'
            subst hy hx
            dsimp [AntisymmRel] at h
            exact AntisymmRel.ge (id (And.symm h))
          subst hy hx
          simp_all only [le_refl, Subtype.forall, coe_mem, mem_filter, Finset.mem_univ, true_and, Quotient.eq,
            AntisymmRel.setoid_r, Subtype.exists, st, I']
        ·
          subst hy hx
          simp_all only [Subtype.forall, mem_filter, Finset.mem_univ, true_and, Quotient.eq, AntisymmRel.setoid_r,
            Subtype.exists, st, I']

      · constructor
        · exact hs
        · intro ss x
          intro h
          simp_all only [Subtype.forall, Finset.mem_image, mem_filter, Finset.mem_univ,
            true_and, Quotient.eq, Subtype.exists, I', st]
          use x
          use (ss h)
          constructor
          · intro aa bb
            intro hh
            dsimp [setoid_preorder] at hh
            dsimp [AntisymmRel] at hh
            specialize hhs x
            have : x ∈ V := ss h
            specialize hhs this
            specialize hhs h
            specialize hhs aa bb
            simp_all only [forall_const, st, I']
          ·
            simp_all only [AntisymmRel.setoid_r, st, I']
            rfl

    · intro hi --sはsetoidのidealで、その性質がaに入っている。
      obtain ⟨I, hI⟩ := hi --hIに同値類の順序が入っている。
      constructor --sは、Iの半順序のideal。
      · simp_all only
      · intro v hv
        intro w a
        obtain ⟨left, right⟩ := hI
        --left  ∀ q ∈ I, ∀ q' ≤ q, q' ∈ I
        --right s ⊆ V ∧ ∀ (hs : s ⊆ V) (x : α) (h : x ∈ s), ⟦⟨x, ⋯⟩⟧ ∈ I
        --obtain ⟨val, property⟩ := v
        --obtain ⟨val_1, property_1⟩ := w
        let q:= Quotient.mk st v
        let q':= Quotient.mk st w
        --simp_all only [forall_true_left]
        --simp_all only
        show ↑w ∈ s
        --rcases Quotient.exists_rep q with ⟨y, hy⟩ --xはq'の代表元。
        --rcases Quotient.exists_rep q' with ⟨x, hx⟩ --xはq'の代表元
        have : q ∈ I := by
          simp_all only [st, q]
          obtain ⟨val, property⟩ := v
          obtain ⟨val_1, property_1⟩ := w
          obtain ⟨left_1, right⟩ := right
          simp_all only [forall_true_left, st]
        have qI: q' ∈ I := by
          -- Add necessary proof steps here
          specialize left q this q' a
          exact left
        dsimp [q'] at qI
        --preorderとorderの関係を使う必要があるかも。
        rw [← @Quotient.mk''_eq_mk] at qI
        dsimp [setoid_preorder] at qI
        have :q' ≤ q := by
          simp_all only [st, q, q']
          exact a
        have wv: w ≤ v := by
          simp_all only [q', st, q]
        have aS: {a:V | (Quotient.mk st a) = q'}.image Subtype.val  ⊆ s := by
          intro x
          intro h
          simp_all only [mem_image, Subtype.val, mem_filter, Finset.mem_univ, true_and]
          show x ∈ ↑s
          obtain ⟨y, hy⟩ := Quotient.exists_rep q'
          sorry
        have : w ∈ {a:V | (Quotient.mk st a) = q'} := by
          simp_all only [mem_image, Subtype.val, mem_filter, Finset.mem_univ, true_and]
          simp_all only [Quotient.eq, AntisymmRel.setoid_r, Set.image_subset_iff, mem_setOf_eq, q', st, q]
          obtain ⟨val, property⟩ := v
          obtain ⟨val_1, property_1⟩ := w
          obtain ⟨left_1, right⟩ := right
          simp_all only [forall_true_left, st]
          simp_all only [st]
          rfl
        have : w.val ∈ {a:V | (Quotient.mk st a) = q'}.image Subtype.val := by
          simp_all only [mem_image, Subtype.val, mem_filter, Finset.mem_univ, true_and]
          simp_all only [Quotient.eq, AntisymmRel.setoid_r, Set.image_subset_iff, mem_setOf_eq, Subtype.exists,
            exists_and_right, exists_eq_right, Subtype.coe_eta, coe_mem, exists_const, q', st, q]
        have : w.val ∈ s := by
          exact aS this
        exact this
