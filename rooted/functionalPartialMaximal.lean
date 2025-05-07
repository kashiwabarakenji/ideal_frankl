--import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
--import Mathlib.Order.Cover
--import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.functionalTraceIdeal2

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]


-- ここから下は、traceに関係ないので移動したほうがいいかも。Setup_poの極大要素に関係がある。functionalPartialMaximalとかか。
open Function Finset

def po_maximal (s: Setup_po α) (x: s.V) : Prop := ∀ y, s.po.le x y → x = y

lemma po_maximal_lem (s: Setup_po α) (x: s.V) :
  po_maximal s x ↔ s.f x = x :=
by
  constructor
  · intro h
    have h1 : s.po.le x (s.f x) := by
      apply (s.order x (s.f x)).1
      use 1
      simp_all only [Function.iterate_one]
    have h2 : x = s.f x := by
      apply h
      exact h1
    exact id (Eq.symm h2)
  · intro hfx
    dsimp [po_maximal]
    intro y hxy
    -- `≤`  ⇒  `reach`
    have hreach : reach s.f x y := (s.order x y).2 hxy
    rcases hreach with ⟨n, hn⟩
    -- show every iterate of `f` fixes `x`
    have h_iter : s.f^[n] x = x := by
      induction n with
      | zero       => simp
      | succ n ih  =>
          exact Function.iterate_fixed hfx (n + 1)
    -- rewrite the equality obtained from `reach`
    simpa [h_iter] using hn

/--
`f : α → α` を `Fintype` 上で反復すると、
`0,1,…,Fintype.card α` のうち 2 つの反復が一致する。
-/
lemma exists_eq_iterate {α : Type u} [DecidableEq α] [Fintype α]
  (f : α → α) (a : α) :
  ∃ m n : ℕ, m < n ∧ f^[m] a = f^[n] a := by
  classical
  -- Put `N = |α|`
  set N : ℕ := Fintype.card α with hN
  -- Consider g : Fin (N+1) → α,  k ↦ f^[k] a
  let g : Fin (N + 1) → α := fun k => (f^[k]) a

  ----------------------------------------------------------------
  -- 1.  g  は単射になれない (鳩ノ巣原理)
  ----------------------------------------------------------------
  have h_not_inj : ¬Injective g := by
    intro hg
    -- 単射なら |Fin (N+1)| ≤ |α|
    have h_card := Fintype.card_le_of_injective g hg
    -- |Fin (N+1)| = N+1
    have : N + 1 ≤ N := by
      simp [hN, Fintype.card_fin]
      simp_all only [Fintype.card_fin, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, N, g]
    exact (Nat.not_succ_le_self N) this

  ----------------------------------------------------------------
  -- 2.  非単射性 → 同じ像を持つ異なる添字が存在
  ----------------------------------------------------------------
  have h_exists_pair :
      ∃ i j : Fin (N + 1), i ≠ j ∧ g i = g j := by
    -- `not_injective_iff` : ¬Inj f ↔ ∃ x y, f x = f y ∧ x ≠ y
    simp [Function.not_injective_iff]
    dsimp [Injective] at h_not_inj
    push_neg at h_not_inj
    obtain ⟨i, j, hEq⟩ := h_not_inj
    use i, j
    rw [and_comm]
    exact hEq

  -- 取り出し，順序を m < n に整える
  rcases h_exists_pair with ⟨i, j, hne, hEq⟩
  -- choose (m,n) with m < n
  cases lt_or_gt_of_ne hne with
  | inl hij =>
      exact ⟨i, j, hij, by
        -- g i = g j は そのまま iterate equality
        simpa [g] using hEq⟩
  | inr hji =>
      -- swap  i j
      exact ⟨j, i, hji, by
        simp [g, hEq]
        ⟩

lemma po_maximal_reachable (s : Setup_po α) (y : s.V):
 ∃ x, po_maximal s x ∧ reach s.f y x :=
by
  -- x は、yの上を要素を辿っていって、s.f x = x になるもの。
  -- f^[n] yでnを増やすと有限の大きさなので、必ず、どこかで、m < nで、f^[m] = f^[n]になる。
  --このとき、 半順序のantisymmetryより、f^[m] y <= f^[m+1] y <= f^[n] yより、
  -- f^[m] y = f^[m+1] yとなる。
  --x = f^[m] yとすればよい。
  obtain ⟨m,n,hmn,heq⟩ :=
    exists_eq_iterate (s.f) y   -- m < n かつ f^[m] y = f^[n] y
  set g : ℕ → s.V := fun k => (s.f^[k]) y with hg

  -- 2. 連鎖   g m ≤ g (m+1) ≤ … ≤ g n = g m
  --    antisymmetry から g m = g (m+1) が従う
  have h_step :
      s.po.le (g m) (g (m+1)) := by
    -- reach (1 step) → ≤
    have : reach s.f (g m) (g (m+1)) := by
      refine ⟨1,?_⟩
      simp [hg, iterate_one, iterate_succ_apply']  -- f^[m+1] = f^[1] (f^[m])
    simpa [hg] using (s.order _ _).1 this

  have h_chain :
      s.po.le (g (m+1)) (g n) := by
    -- reach (n-(m+1)) steps → ≤
    have : reach s.f (g (m+1)) (g n) := by
      refine ⟨n - (m+1), ?_⟩
      -- iterate_add to split the exponent
      have : (s.f^[n - (m+1)]) ((s.f^[m+1]) y) = (s.f^[n]) y := by
        simp [iterate_add, hg, add_comm]
        show s.f^[n - (m + 1)] (s.f^[m] (s.f y)) = s.f^[n] y
        have h := Nat.add_sub_cancel' (Nat.succ_le_of_lt hmn)
        rw [←@comp_apply _ _ _ (s.f^[m]) s.f y ]
        rw [←Function.iterate_succ]
        rw [←@comp_apply _ _ _ s.f^[n - (m + 1)] (s.f^[m.succ]) y ]
        rw [←iterate_add]
        simp_all only [iterate_succ, comp_apply, Nat.succ_eq_add_one, g]
        obtain ⟨val, property⟩ := y
        rw [Nat.sub_add_cancel hmn]
      simpa [hg] using this
    let so := (s.order _ _).1 this
    simp
    exact so

  -- g m = g n なので antisymmetry で g m = g (m+1)
  have h_fix : (s.f^[m] y) = (s.f^[m+1] y) := by
    have : s.po.le (g m) (g (m+1)) ∧ s.po.le (g (m+1)) (g m) := by
      have h₁ := h_step
      have h₂ : s.po.le (g (m+1)) (g m) := by
        simp_all only [iterate_succ, comp_apply, g]

      exact And.intro h₁ h₂

    have := s.po.le_antisymm (g m) (g (m+1)) this.1 this.2
    simpa [hg, iterate_succ_apply'] using this

  -- 3. 目的の元 `x`
  let x : s.V := ⟨ (s.f^[m] y).val, by
    -- g m ∈ s.V  は自明
    simp_all only [iterate_succ, comp_apply, le_refl, coe_mem, g]⟩

  have fx_eq : s.f x = x := by
    -- unwrap the subtype / use h_fix
    --apply Subtype.ext
    --show ↑(s.f x) = x.val
    rw [iterate_succ_apply'] at h_fix
    exact id (Eq.symm h_fix)

  have h_max : po_maximal s x := by
    -- 既に示してある補題 po_maximal_lem
    have := (po_maximal_lem s x).mpr fx_eq
    simpa using this

  have h_reach : reach s.f y x := by
    -- x = f^[m] y なので reach (m steps)
    refine ⟨m, ?_⟩
    -- unfold x
    simp_all only [iterate_succ, comp_apply, Subtype.coe_eta, g, x]

  exact ⟨x, h_max, h_reach⟩

lemma po_maximal_reachable_eq (s : Setup_po α) (y : s.V):
 ∀ x1 x2, (po_maximal s x1 ∧ reach s.f y x1 ) →
          (po_maximal s x2 ∧ reach s.f y x2) →
          x1 = x2 :=
by
  intro x₁ x₂ h₁ h₂
  rcases h₁ with ⟨hmax₁, ⟨k₁, hk₁⟩⟩
  rcases h₂ with ⟨hmax₂, ⟨k₂, hk₂⟩⟩
  -- 反復回数を比較
  cases le_or_gt k₁ k₂ with
  | inl hle =>
      -- k₁ ≤ k₂ なら x₁ → x₂ に可達
      have hreach : reach s.f x₁ x₂ := by
        have : (s.f^[k₂ - k₁]) x₁ = x₂ := by
          -- 書き換えに `iterate_add_apply`
          have : (s.f^[k₁ + (k₂ - k₁)]) y = x₂ := by
            simpa [Nat.add_sub_cancel' hle] using hk₂
          have : (s.f^[k₂ - k₁]) ((s.f^[k₁]) y) = x₂ := by
            rw [←iterate_add_apply]
            have :k₂ - k₁ + k₁ = k₂ := by
              exact Nat.sub_add_cancel hle
            rw [this]
            exact hk₂

          simpa [hk₁] using this
        exact ⟨k₂ - k₁, this⟩
      -- 可達性 ↔ ≤ で比較
      have hle₁₂ : s.po.le x₁ x₂ := (s.order _ _).1 hreach
      -- 極大性から等号
      exact (hmax₁ x₂ hle₁₂)
  | inr hgt =>
      -- 対称な場合 k₂ ≤ k₁
      have hreach : reach s.f x₂ x₁ := by
        have : (s.f^[k₁ - k₂]) x₂ = x₁ := by
          have : (s.f^[k₂ + (k₁ - k₂)]) y = x₁ := by
            simpa [Nat.add_sub_cancel' (Nat.le_of_lt hgt)] using hk₁
          have : (s.f^[k₁ - k₂]) ((s.f^[k₂]) y) = x₁ := by
            rw [←iterate_add_apply]
            have :k₁ - k₂ + k₂ = k₁ := by
              exact Nat.sub_add_cancel (Nat.le_of_lt hgt)
            rw [this]
            exact hk₁

          simpa [hk₂] using this
        exact ⟨k₁ - k₂, this⟩
      have hle₂₁ : s.po.le x₂ x₁ := (s.order _ _).1 hreach
      exact (hmax₂ x₁ hle₂₁).symm

noncomputable def proj_max (s: Setup_po α) (v : {x : α // x ∈ s.V}) : {x : α // x ∈ s.V} :=
  Classical.choose (po_maximal_reachable s v)

def projr (s: Setup_po α)(v w : {x : α // x ∈ s.V}) : Prop := proj_max s v = proj_max s w

instance proj_setoid {α : Type} [Fintype α] [DecidableEq α] (s: Setup_po α) [DecidableRel (projr s)]: Setoid {x : α // x ∈ s.V} where
  r  := projr s
  iseqv :=
    ⟨
      -- refl: ∀ (v : {x : α // x ∈ s.V}), projr s v v
      fun (v : {x : α // x ∈ s.V}) => rfl,
      -- symm: ∀ (v w : {x : α // x ∈ s.V}), projr s v w → projr s w v
      @fun (v w : {x : α // x ∈ s.V}) (h : projr s v w) => Eq.symm h,
      -- trans: ∀ (v w u : {x : α // x ∈ s.V}), projr s v w → projr s w u → projr s v u
      fun {v : {x : α // x ∈ s.V}} {w : {x : α // x ∈ s.V}} {u : {x : α // x ∈ s.V}}
          (h₁ : projr s v w) (h₂ : projr s w u) => Eq.trans h₁ h₂
    ⟩

lemma proj_max_maximal (s: Setup_po α) (v : {x : α // x ∈ s.V}) :
  po_maximal s (proj_max s v) := by
  -- proj_max は po_maximal_reachable の選択肢の一つ
  obtain ⟨x, hmax, _⟩ := Classical.choose_spec (po_maximal_reachable s v)
  -- x = proj_max s v を示す
  obtain ⟨val, property⟩ := v
  exact x


lemma reach_maximal (s: Setup_po α) (v : {x : α // x ∈ s.V}) : reach s.f v (proj_max s v) := by
  -- proof for reachability from v to proj_max s v
  dsimp [proj_max]
  --dsimp [po_maximal_reachable]
  obtain ⟨x, n, hx⟩ := Classical.choose_spec (po_maximal_reachable s v)
  dsimp [reach]
  use n

--コンポーネントが等しいことと、極大要素が等しいことは同値。
lemma proj_max_quotient (s: Setup_po α) (x y : {x : α // x ∈ s.V}) :
  proj_max s x = proj_max s y ↔ Quotient.mk (proj_setoid s) x = Quotient.mk (proj_setoid s) y := by
  -- proj_max は po_maximal_reachable の選択肢の一つ
  apply Iff.intro
  · intro h
    dsimp [proj_max] at h
    simp_all only [Quotient.eq]
    exact h
  · intro h
    dsimp [proj_max]
    --obtain ⟨x, hmax, _⟩ := Classical.choose_spec (po_maximal_reachable s x)
    --obtain ⟨y, hmax, _⟩ := Classical.choose_spec (po_maximal_reachable s y)
    simp_all only [Quotient.eq]
    exact h

--同値類から極大要素を取り出す。proj_max_quotientはつかってない。
noncomputable def proj_max_of_quot
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup_po α) :
  Quotient (proj_setoid s) →
    {x : α // x ∈ s.V} :=
  Quotient.lift
    (fun v : {x : α // x ∈ s.V} => proj_max s v)
    (by
      -- `projr s v w` はまさに
      -- `proj_max s v = proj_max s w` なのでそのまま使える
      intro v w h
      simpa using h)

@[simp] lemma proj_max_of_quot_mk
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Setup_po α) (v : {x : α // x ∈ s.V}) :
  proj_max_of_quot s ⟦v⟧ = proj_max s v := rfl

--yの極大要素proj_maxが本当に極大要素で、上にあること。
theorem proj_max_spec (s : Setup_po α) (y : s.V) :
  po_maximal s (proj_max s y) ∧ reach s.f y (proj_max s y) :=
  Classical.choose_spec (po_maximal_reachable s y)

lemma proj_max_unique (s : Setup_po α) {y x : s.V}
  (h : po_maximal s x ∧ reach s.f y x) :
  proj_max s y = x := by
  -- choose_spec で proj_max の性質を取り出し
  have hy := proj_max_spec s y
  -- 一意性の補題で同値写像
  exact po_maximal_reachable_eq s y (proj_max s y) x hy h

--大小関係がある場合は、対応する極大要素は等しい。
lemma proj_max_order (s: Setup_po α) (x y : {x : α // x ∈ s.V})(od:s.po.le x y) :
 proj_max s x = proj_max s y := by
  -- proj_max は po_maximal_reachable の選択肢の一つ
  dsimp [proj_max]
  rw [←s.order x y] at od
  obtain ⟨xm, hmax, hx⟩ := Classical.choose_spec (po_maximal_reachable s x)
  obtain ⟨ym, hmax, hy⟩ := Classical.choose_spec (po_maximal_reachable s y)
  have : reach s.f y (proj_max s y) := by
    exact reach_maximal s y
  have :reach s.f x (proj_max s y) := by
    --reachのtransitivityの定理があるはず。
    exact reach_trans s.f od this
  apply proj_max_unique s
  constructor
  · simp_all only
  · exact this

--大小関係がある場合は、対応するコンポーネントは等しい。
lemma quotient_order (s: Setup_po α) (x y : {x : α // x ∈ s.V}) (od:s.po.le x y):
  Quotient.mk (proj_setoid s) x = Quotient.mk (proj_setoid s) y := by
  -- proj_max は po_maximal_reachable の選択肢の一つ
  apply (proj_max_quotient s x y).mp
  exact proj_max_order s x y od


------------------------------------------------------------
-- 1.  補題：極大なら proj_max s x = x
------------------------------------------------------------

lemma proj_max_eq_of_maximal
    (s : Setup_po α) (x : s.V) (hmax : po_maximal s x) :
    proj_max s x = x := by
  dsimp [proj_max]
  apply proj_max_unique s
  constructor
  · exact hmax
  · dsimp [reach]
    use 0
    simp
--end Setup_po
