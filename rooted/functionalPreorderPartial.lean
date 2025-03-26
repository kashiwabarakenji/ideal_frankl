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
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne
import rooted.functionalCommon
import rooted.functionalPreorder
import rooted.functionalTree


open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]
/-

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
