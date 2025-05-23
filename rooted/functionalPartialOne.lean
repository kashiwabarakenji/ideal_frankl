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
import rooted.DirectProduct
import rooted.functionalPartialMaximal
import rooted.functionalPartialTrace
import rooted.functionalDirectProduct

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

--連結成分がひとつであるときに、極大要素が最大要素になり、次数が1になることを証明したい。
--その要素をtraceしても、ndsが上がらないことを示したい。

------------------------------------------------------------
-- 2.  補題：numClasses = 1 なら Quotient が subsingleton
------------------------------------------------------------

/--
`Finset.card` が 1 の集合は実質的に要素が一つだけなので，
その要素で固定すれば subsingleton が取れる。
-/
private lemma quotient_subsingleton
    (s : Setup_po α)
    (h : numClasses (proj_setoid s) = 1) :
    Subsingleton (Quotient (proj_setoid s)) := by
  -- `numClasses` の実体
  dsimp [numClasses] at h
  -- `Finset.card_eq_one` で代表元 `q0` を取る
  --card_eq_one.mp h : ∃ a, Finset.image (Quot.mk ⇑(proj_setoid s)) s.V.attach = {a}

  obtain ⟨q0, hmem⟩ := Finset.card_eq_one.1 h
  -- 以後，どんな `q` も `q0` に等しいことを示す
  have hmem' : Finset.univ.image (Quot.mk (proj_setoid s)) = {q0} :=
  by
    simp_all only [Finset.card_singleton, univ_eq_attach]
    convert hmem
  refine ⟨?eq⟩
  intro q1 q2
  have hq1 : q1 = q0 := by
    have : q1 ∈ (Finset.univ.image (Quot.mk _)) := by
      -- `q1` には必ず代表元が存在する
      rcases Quot.exists_rep q1 with ⟨v, rfl⟩
      simp
    rw [hmem'] at this
    exact Finset.mem_singleton.1 this

    --exact (huniq _ this).trans (by symm; exact rfl)
  have hq2 : q2 = q0 := by
    have : q2 ∈ (Finset.univ.image (Quot.mk _)) := by
      rcases Quot.exists_rep q2 with ⟨v, rfl⟩
      rw [hmem']
      simp
      have hv : v ∈ s.V.attach := by exact mem_attach s.V v
      -- 2) 画像に入る
      have : Quot.mk (proj_setoid s) v ∈ Finset.image (Quot.mk (proj_setoid s)) s.V.attach :=
        Finset.mem_image_of_mem (Quot.mk (proj_setoid s)) hv
      -- 3) image = {q0} なので単一元のメンバーシップから q = q0
      have : Quot.mk (⇑(proj_setoid s)) v ∈ ({q0}:Finset (Quotient (proj_setoid s))) :=
      by
        convert this
        exact id (Eq.symm hmem')
      exact Finset.mem_singleton.1 this

      --exact mem_image.2 ⟨v, by simp, rfl⟩
    apply Finset.mem_singleton.1
    rw [hmem'] at this
    exact this

  simp [hq1, hq2]

------------------------------------------------------------
-- 3.  補題：numClasses = 1 なら ∀y, proj_max s y = proj_max s x
------------------------------------------------------------

private lemma proj_max_eq_of_one_class
    (s : Setup_po α) (h : numClasses (proj_setoid s) = 1)
    (x y : {x : α // x ∈ s.V}) :
    proj_max s y = proj_max s x := by
  haveI : Subsingleton (Quotient (proj_setoid s)) :=
    quotient_subsingleton s h
  -- Quotient が subsingleton なら二つの要素は等しい
  have hquot :
      (Quotient.mk (proj_setoid s) x :
        Quotient (proj_setoid s)) =
      Quotient.mk (proj_setoid s) y := Subsingleton.elim _ _
  -- 補題で proj_max の等しさに戻す
  exact (proj_max_quotient s y x).mpr (id (Eq.symm hquot))

------------------------------------------------------------
-- 4.  本命：component_one
------------------------------------------------------------

--外からも使っている。コンポーネントの数が1だと、極大要素を含むhyperedgeが全体集合になること。
theorem component_one
    (s : Setup_po α)
    (h1 : numClasses (proj_setoid s) = 1) :
    ∀ ss : Finset α, ∀ x : s.V,
      (po_closuresystem s).sets ss →
      x.val ∈ ss →
      po_maximal s x →
      ss = s.V := by
  intro ss x hset hx hmax
  -- `ss ⊆ s.V` はセットの定義から得られる
  have hsubset : ss ⊆ s.V := hset.1
  -- 逆向き：`s.V ⊆ ss`
  have hsuperset : s.V ⊆ ss := by
    intro a haV
    -- `a` を `s.V` 型にリフト
    let y : s.V := ⟨a, haV⟩
    -- 1クラス ⇒ `proj_max s y = x`
    have hproj : proj_max s y = x := by
      have := proj_max_eq_of_one_class s h1 x y
      -- `proj_max s x = x`（極大性）に書き換える
      have hxproj : proj_max s x = x :=
        proj_max_eq_of_maximal s x hmax
      simpa [hxproj] using this
    -- `reach y x` → `y ≤ x`
    have hle : s.po.le y x := by
      -- 到達可能性
      have hreach : reach s.f y (proj_max s y) := by
        obtain ⟨_, _, h⟩ := Classical.choose_spec
                                (po_maximal_reachable s y)
        exact reach_maximal s y
      have : reach s.f y x := by
        simpa [hproj] using hreach
      exact (s.order y x).1 this
    -- ideal の条件で `y ∈ ss`
    have hdown := hset.2 x hx y hle
    simpa using hdown
  -- 2方向の包含で Finset 等号
  exact Finset.Subset.antisymm hsubset hsuperset

--全体集合からmaximalな要素を除いたものがidealになること。
--連結成分の数の仮定は必要ない。
private lemma hasgroundminusone
  (s : Setup_po α) (x : s.V) (mx :po_maximal s x):
    (po_closuresystem s).sets (s.V.erase x) :=
by

  refine And.intro ?subset ?ideal

  /- ① 包含 `erase ⊆ V` はライブラリ補題で済む -/
  · exact Finset.erase_subset _ _

  /- ② ideal 条件 -/
  · intro v hv w hw
    -- `hv` : v.val ∈ s.V.erase x
    -- `hw` : s.po.le w v
    -- 目標 : w.val ∈ s.V.erase x
    -- まず `hv` から `v.val ≠ x` を取り出す
    have hvne : (v : α) ≠ x := (Finset.mem_erase.1 hv).1

    -- `w = x` かどうかで場合分け
    by_cases hwx : (w : s.V) = x
    · -- (1) もし `w = x` なら `x ≤ v` なので極大性と矛盾
      have hxv : s.po.le x v := by
        simpa [hwx] using hw
      have hxeqv : (x : s.V) = v := mx v hxv
      have : (v : α) = x :=
      by
        apply congrArg Subtype.val
        subst hwx hxeqv
        simp_all only [le_refl, mem_erase, ne_eq, not_true_eq_false, coe_mem, and_true]
      exact (hvne this).elim          -- 矛盾 → このケースは起こらない
    · -- (2) `w ≠ x` なら下方閉なので w も erase に入る
      --   `w.val ∈ s.V` は `w.property`
      --   `w.val ≠ x` は `w ≠ x` から導ける
      have hwne : (w : α) ≠ x := by
        intro hval
        apply hwx
        apply Subtype.ext
        exact hval
      exact (Finset.mem_erase).2 ⟨hwne, w.property⟩

private lemma po_trace_le_iff
    (s : Setup_po α) (x : s.V) (mx : po_maximal s x)
    (nontriv : s.V.card ≥ 2)
    {a b : s.V}
    (ha : (a : α) ≠ x) (hb : (b : α) ≠ x) :
  let a' : (po_trace s x mx nontriv).V :=
        ⟨a, by
          -- `a` は `V.erase x` に入っている
          exact Finset.mem_erase.mpr ⟨ha, a.property⟩⟩
  let b' : (po_trace s x mx nontriv).V :=
        ⟨b, by
          exact Finset.mem_erase.mpr ⟨hb, b.property⟩⟩
  (po_trace s x mx nontriv).po.le a' b'
    ↔ s.po.le a b := by
  -- `simp [po_trace]` 展開のあと，両辺が文字通り同じ式になる
  simp
    [ po_trace                       -- ← let 展開で `le` が現れる
    , Finset.mem_erase, ha, hb       -- 使い切るための `simp` データ
    ]

private lemma not_mem_of_subset_erase
  {α : Type _} [DecidableEq α]  -- ← here
  {x : α} {ss ground : Finset α}
  (h : ss ⊆ ground.erase x) :
  x ∉ ss := by
  intro hx
  have : x ∈ ground.erase x := h hx
  -- `Finset.mem_erase.1` : `a ∈ s.erase a ↔ ¬ a = a ∧ a ∈ s`
  exact (Finset.mem_erase.1 this).1 rfl

private lemma trace_sets_iff (s  : Setup_po α) (conn  : numClasses (proj_setoid s) = 1)  (x  : s.V) (mx : po_maximal s x) (nontriv : s.V.card ≥ 2)(ss : Finset α) :
    (po_closuresystem (po_trace s x mx nontriv)).sets ss
    ↔ (po_closuresystem s).sets ss ∧ ss ≠ s.V :=
by
  let t := po_trace s x mx nontriv
  have tV : t.V = s.V.erase x := by
    simp [t, po_trace]

  ------------------------------------------------------------------
  -- → 方向
  ------------------------------------------------------------------
  have forward :
      (po_closuresystem t).sets ss →
        (po_closuresystem s).sets ss ∧ ss ≠ s.V := by
    intro h_t
    -- 1. ground 包含
    have h_sub_erase : ss ⊆ s.V.erase x := by
      have : ss ⊆ t.V := (po_closuresystem t).inc_ground ss h_t
      simpa [tV] using this
    have h_sub_V : ss ⊆ s.V := by
      exact subset_trans h_sub_erase (Finset.erase_subset _ _)

    -- 2. `x ∉ ss` かつ `ss ≠ s.V`
    have hx_not : (x : α) ∉ ss :=
    by
      let nms :=  not_mem_of_subset_erase h_sub_erase
      exact nms
    have h_ne : ss ≠ s.V := by
      intro h_eq
      have : (x : α) ∈ ss := by
        have : (x : α) ∈ s.V := x.property
        simp [h_eq]
      exact hx_not this

    -- 3. 下方閉 (ideal 条件) を元の半順序へエスカレーション
    have h_down : ∀ v : s.V, v.1 ∈ ss →
        ∀ w : s.V, s.po.le w v → w.1 ∈ ss := by
      intro v hv w hw
      -- `v ≠ x` は `hv` と `hx_not` から分かる
      by_cases hvx : (v : α) = x
      · exfalso
        have : (x : α) ∈ ss := by simpa [hvx] using hv
        exact hx_not this
      -- 以降 `v ≠ x`
      -- trace 型へキャスト
      have hv_in : (v : α) ∈ s.V.erase x :=
        h_sub_erase hv
      have w_case : (w : α) ≠ x := by
        by_contra hwx
        have hle : s.po.le x v := by
          simp_all only [ne_eq, mem_erase, not_false_eq_true, coe_mem, and_self, t]
          obtain ⟨val, property⟩ := x
          obtain ⟨val_1, property_1⟩ := v
          obtain ⟨val_2, property_2⟩ := w
          subst hwx
          simp_all only

        have h_eq : (x : s.V) = v := mx v hle
        have : (v : α) = x :=
        by
          apply congrArg Subtype.val
          exact id (Eq.symm h_eq)
        exact hvx this
      have hw_in : (w : α) ∈ s.V.erase x := by
        exact Finset.mem_erase.mpr ⟨w_case, w.property⟩

      -- Trace world の要素
      let v'  : t.V := ⟨v, hv_in⟩
      let w'  : t.V := ⟨w, hw_in⟩
      -- ≤ 変換
      have h_le' : t.po.le w' v' := by
        have := (po_trace_le_iff s x mx nontriv
                    (a:=⟨w, w.property⟩) (b:=⟨v, v.property⟩)
                    w_case hvx).mpr hw
        simpa [w', v'] using this
      -- trace イデアル性から結論
      have : w.1 ∈ ss := by
        have hv' : v'.1 ∈ ss := by
          dsimp [v'] at *
          simpa using hv
        have := h_t.2 v' hv' w' h_le'
        simpa [w'] using this
      exact this

    exact And.intro (And.intro h_sub_V h_down) h_ne

  ------------------------------------------------------------------
  -- ← 方向
  ------------------------------------------------------------------
  have backward :
      (po_closuresystem s).sets ss ∧ ss ≠ s.V →
        (po_closuresystem t).sets ss := by
    rintro ⟨h_s, h_ne⟩
    -- `x ∉ ss` （さもなくば component_one に反する）
    have hx_not : (x : α) ∉ ss := by
      by_contra hx
      have h_eq := component_one s conn ss x h_s hx mx
      exact h_ne h_eq
    -- 1. ground 包含: ss ⊆ V.erase x
    have h_sub_erase : ss ⊆ s.V.erase x := by
      intro a ha
      have haV : a ∈ s.V := (h_s.1 ha)
      by_cases hax : a = x
      · exfalso
        have : (x : α) ∈ ss := by simpa [hax] using ha
        exact hx_not this
      · exact Finset.mem_erase.mpr ⟨hax, haV⟩

    -- 2. 下方閉を trace 側で示す
    have h_down_t :
        ∀ v' : t.V, v'.1 ∈ ss →
          ∀ w' : t.V, t.po.le w' v' → w'.1 ∈ ss := by
      intro v' hv w' hw
      -- 元の型へ戻す
      let v : s.V :=
        ⟨v', (Finset.mem_of_mem_erase v'.property)⟩
      let w : s.V :=
        ⟨w', (Finset.mem_of_mem_erase w'.property)⟩
      have hv_s : v.1 ∈ ss := by
        dsimp [v] at *
        simpa using hv
      -- ≤ の変換
      have h_le : s.po.le w v := by
        have := (po_trace_le_iff s x mx nontriv
                    (a:=w) (b:=v)
                    (by
                      intro h; exact (Finset.mem_erase.1 w'.property).1 h)
                    (by
                      intro h; exact (Finset.mem_erase.1 v'.property).1 h)).1 hw
        simpa using this
      -- 元のイデアル性
      have := h_s.2 v hv_s w h_le
      simpa [w] using this

    -- 3. まとめて `sets`
    exact And.intro h_sub_erase h_down_t

  ------------------------------------------------------------------
  -- 結論
  ------------------------------------------------------------------
  exact ⟨forward, backward⟩

--sectionは、下のvariableの設定のために使っているのかも。
section numberof

variable {α : Type _} [Fintype α] [DecidableEq α]

variable (s : Setup_po α)
variable (x  : s.V) (mx : po_maximal s x)
variable (conn : numClasses (proj_setoid s) = 1)
variable (nontriv : s.V.card ≥ 2)



/------------------------------------------------------------
  補助：SetFamily.number_of_hyperedges を展開しやすくする
------------------------------------------------------------/

noncomputable
def ideals (F : SetFamily α) [DecidablePred F.sets] : Finset (Finset α) :=
  F.ground.powerset.filter F.sets

------------------------------------------------------------------------
-- 1. 名前を短く
------------------------------------------------------------------------

abbrev Fₛ  : ClosureSystem α := po_closuresystem s
abbrev t   : Setup_po α      := (po_trace s x mx nontriv)
abbrev Fₜ  : ClosureSystem α := po_closuresystem (po_trace s x mx nontriv)

noncomputable
instance : DecidablePred (Fₛ s).sets := Classical.decPred _
noncomputable
instance : DecidablePred (Fₜ s x mx nontriv).sets := Classical.decPred _

--lemma test_conn : conn = conn := by rfl

------------------------------------------------------------------------
-- 2. `Fₛ.ideals` と `Fₜ.ideals` の対応
------------------------------------------------------------------------
private lemma ideals_eq_erase (s : Setup_po α) (conn  : numClasses (proj_setoid s) = 1)(x  : s.V) (mx : po_maximal s x) (nontriv : s.V.card ≥ 2):
    (ideals (po_closuresystem (po_trace s x mx nontriv)).toSetFamily) =
      (ideals (po_closuresystem s).toSetFamily).erase (s.V) := by
  -- 記号を開く
  dsimp [ideals]
  -- ground 同定
  have tV : (po_trace s x mx nontriv).V = s.V.erase x := by
    simp [po_trace]
  -- convenience abbreviations
  set Iₛ : Finset (Finset α) :=
      (s.V.powerset).filter (po_closuresystem s).sets with hIₛ
  set Iₜ : Finset (Finset α) :=
      ((s.V.erase x).powerset).filter
        (po_closuresystem (po_trace s x mx nontriv)).sets with hIₜ
  -- 2 ⊆ 関係：`Iₜ` は `Iₛ` から ground を除いたもの
  have sub :
      Iₜ ⊆ Iₛ.erase (s.V) := by
    intro ss hss
    -- `ss ∈ Iₜ` を展開
    have h_memₜ :
        ss ∈ (s.V.erase x).powerset ∧
        (Fₜ s x mx nontriv).sets ss := by
      simpa [hIₜ] using (Finset.mem_filter.1 hss)
    have h_setsₜ := h_memₜ.2
    have h_sub : ss ⊆ s.V.erase x :=
      (Finset.mem_powerset.1 h_memₜ.1)
    -- trace_sets_iff で `Fₛ.sets` ＋ `ss ≠ s.V`
    have h_setsₛ_and_ne :
        (Fₛ s).sets ss ∧ ss ≠ s.V := by
      have := (trace_sets_iff s conn x mx nontriv ss).1 h_setsₜ
      exact this
    -- まとめて `ss ∈ Iₛ` かつ `ss ≠ s.V`
    have h_in_Iₛ : ss ∈ Iₛ := by
      have hp : ss ∈ s.V.powerset := by
        -- `ss ⊆ s.V` は `erase` 包含から
        have : ss ⊆ s.V := subset_trans h_sub (Finset.erase_subset _ _)
        exact (Finset.mem_powerset.2 this)
      simp [hIₛ, hp, h_setsₛ_and_ne.1]
    -- `erase` 条件
    have : ss ≠ s.V := h_setsₛ_and_ne.2
    show ss ∈ Iₛ.erase (s.V)
    · exact Finset.mem_erase.2 ⟨this, h_in_Iₛ⟩
  -- 逆 ⊆ ：`Iₛ` から ground を除いたものはみな `Iₜ`
  have sup :
      Iₛ.erase (s.V) ⊆ Iₜ := by
    intro ss hss
    have ⟨hne, hIₛmem⟩ := Finset.mem_erase.1 hss
    -- `ss` は元の powerset に属しイデアル
    have h_setsₛ : (Fₛ s).sets ss := by
      have := (Finset.mem_filter.1 hIₛmem).2
      simpa [Fₛ] using this
    -- `x ∉ ss` （さもなくば component_one で全体集合）
    have hx_not : (x : α) ∉ ss := by
      by_contra hx
      have h_eq := component_one s conn ss x h_setsₛ hx mx
      exact hne h_eq
    -- まず `ss ⊆ s.V.erase x`
    have h_sub : ss ⊆ s.V.erase x := by
      intro a ha
      have haV : a ∈ s.V :=
      by
        simp_all [Iₛ, Iₜ]
        obtain ⟨val, property⟩ := x
        simp_all only
        exact hIₛmem ha

      by_cases hax : a = x
      · exfalso
        exact hx_not (by simpa [hax] using ha)
      · exact Finset.mem_erase.2 ⟨hax, haV⟩
    -- trace_sets_iff → `Fₜ.sets ss`
    have h_setsₜ :
        (Fₜ s x mx nontriv).sets ss := by
      have : (Fₛ s).sets ss ∧ ss ≠ s.V := by
        exact ⟨h_setsₛ, hne⟩
      exact (trace_sets_iff s conn x mx nontriv ss).2 this
    --  membership in `Iₜ`
    have h_in_powerset : ss ∈ (s.V.erase x).powerset := by
      exact (Finset.mem_powerset.2 h_sub)
    have : ss ∈ Iₜ := by
      simp_all only [ge_iff_le, mem_erase, ne_eq, not_false_eq_true, mem_filter, Finset.mem_powerset, and_true,
        true_and, and_self, Iₜ, Iₛ]
    exact this
  -- 集合（Finset）同値
  exact Finset.Subset.antisymm sub sup
  -- `simp` に渡すため `Iₜ` と `Iₛ.erase _` に戻す

------------------------------------------------------------------------
-- 3. カードを比較して「ちょうど 1 減る」
------------------------------------------------------------------------
lemma number_of_hyperedges_trace (s : Setup_po α) (conn  : numClasses (proj_setoid s) = 1)(x  : s.V) (mx : po_maximal s x) (nontriv : s.V.card ≥ 2):
 (po_closuresystem s).toSetFamily.number_of_hyperedges =
    (po_closuresystem (po_trace s x mx nontriv)).toSetFamily.number_of_hyperedges +1 :=
  -- 展開
by
  dsimp [SetFamily.number_of_hyperedges]
  --dsimp [po_closuresystem]
  -- `card` の計算：erase で 1 つ減る

  -- `Finset.card_erase_add_one` : |erase| + 1 = |S|
  have h_card :
      ((ideals (po_closuresystem s).toSetFamily).erase (s.V)).card + 1 =
        (ideals (po_closuresystem s).toSetFamily).card := by
    apply Finset.card_erase_add_one
    -- ground イデアルは確かにリストに入っている
    have h_ground_sets : (Fₛ s).sets s.V :=
      (Fₛ s).has_ground
    have h_mem :
        s.V ∈ (s.V.powerset).filter (Fₛ s).sets := by
      have hp : s.V ∈ s.V.powerset :=
        (Finset.mem_powerset.2 (Finset.Subset.refl _))
      simpa [ideals, Fₛ] using
        (Finset.mem_filter.2 ⟨hp, h_ground_sets⟩)
    simp [ideals, Fₛ]
    simp_all only [ge_iff_le, mem_filter, Finset.mem_powerset, subset_refl, and_self, and_true]
    obtain ⟨val, property⟩ := x
    rfl
  -- Int に直してゴール完了
  have : Int.ofNat ((ideals (po_closuresystem s).toSetFamily).card)
        = Int.ofNat ((ideals (po_closuresystem s).toSetFamily).erase (s.V)).card + 1 := by
    simpa [Int.ofNat_add, Int.ofNat_one] using congrArg Int.ofNat h_card.symm
  let iee := ideals_eq_erase s conn x mx nontriv
  symm
  ring_nf

  have goal₁ : 1 +  Int.ofNat #((ideals (po_closuresystem s).toSetFamily).erase s.V) = Int.ofNat #(ideals (po_closuresystem s).toSetFamily) := by
    rw [add_comm]
    simp_all only [ge_iff_le, Int.ofNat_eq_coe]

  dsimp [ideals] at goal₁
  simp_all only [ge_iff_le, Int.ofNat_eq_coe]
  obtain ⟨val, property⟩ := x
  convert goal₁

private lemma total_size_of_hyperedge_trace
  (s : Setup_po α)
  (conn  : numClasses (proj_setoid s) = 1)
  (x : s.V) (mx : po_maximal s x)
  (nontriv : s.V.card ≥ 2) :
  (po_closuresystem s).toSetFamily.total_size_of_hyperedges
    = (po_closuresystem (po_trace s x mx nontriv)).toSetFamily.total_size_of_hyperedges
      + s.V.card := by
  -- 1) 定義を展開し、`ideals` を導入
  dsimp [SetFamily.total_size_of_hyperedges, ideals]
  let I := ideals (po_closuresystem s).toSetFamily

  -- 2) ground (= s.V) は必ず I に含まれるので erase 後に足し戻す
  have hG : s.V ∈ I := by
    dsimp [ideals]
    -- powerset.filter で ground が残る
    have : s.V ∈ s.V.powerset := by
      apply Finset.mem_powerset.mpr
      exact fun ⦃a⦄ a => a
    simp_all only [ge_iff_le, Finset.mem_powerset, subset_refl, I]
    obtain ⟨val, property⟩ := x
    simp only [ideals]
    simp_all only [mem_filter, Finset.mem_powerset]
    apply And.intro
    · rfl
    · simp only [po_closuresystem, conn]
      simp_all only [subset_refl, coe_mem, implies_true, imp_self, and_self]

  -- 3) sum_erase_add で (I.erase s.V).sum + s.V.card = I.sum
  have h_sum : (I.erase s.V).sum Finset.card + s.V.card = I.sum Finset.card :=
  by
    apply Finset.sum_erase_add
    simp_all only [ge_iff_le, I]

  -- 4) 最終的に `ideals_eq_erase` と `Int.ofNat_add` を使って終わり

  simp [ideals_eq_erase s conn x mx nontriv, Int.ofNat_add]
  let cih := congrArg Int.ofNat h_sum.symm
  dsimp [I,ideals] at h_sum cih
  convert cih
  · exact
      Eq.symm
        (Nat.cast_sum
          (filter (po_closuresystem s).sets (po_closuresystem s).ground.powerset)
          card)
  · norm_cast
    simp
    let iee := ideals_eq_erase s conn x mx nontriv
    exact congrFun (congrArg Finset.sum iee) fun x => #x

--上の定理の最初の証明。ちょっとだけ長い。あとで消す。
lemma total_size_of_hyperedge_trace2
  (s : Setup_po α)
  (conn  : numClasses (proj_setoid s) = 1)
  (x : s.V) (mx : po_maximal s x)
  (nontriv : s.V.card ≥ 2) :
  (po_closuresystem s).toSetFamily.total_size_of_hyperedges
    = (po_closuresystem (po_trace s x mx nontriv)).toSetFamily.total_size_of_hyperedges
      + s.V.card := by
  -- 1) 定義を展開
  dsimp [SetFamily.total_size_of_hyperedges]

  -- 2) sum_erase_add: erase s.V で消えた部分に s.V.card を足すと元に戻る

  have h_sum :
      ((ideals (po_closuresystem s).toSetFamily).erase s.V).sum Finset.card + s.V.card
        = (ideals (po_closuresystem s).toSetFamily).sum Finset.card := by
    apply Finset.sum_erase_add
    -- ground (= s.V) は必ず ideals に含まれる
    have hG : s.V ∈ ideals (po_closuresystem s).toSetFamily := by
      dsimp [ideals, Fₛ]
      -- s.V ∈ powerset かつ s.V.sets は has_ground
      have hp : s.V ∈ s.V.powerset :=
      by
        apply Finset.mem_powerset.mpr
        simp_all only [ge_iff_le, subset_refl]
      simp [hp, Fₛ]
      simp_all only [ge_iff_le, Finset.mem_powerset, subset_refl]
      obtain ⟨val, property⟩ := x
      apply And.intro
      · rfl
      · unfold po_closuresystem
        simp_all only [subset_refl, coe_mem, implies_true, imp_self, and_self]
    simp [hG]

  -- 3) Nat → Int に持ち上げ
  have h_int :
      Int.ofNat (((ideals (po_closuresystem s).toSetFamily).erase s.V).sum Finset.card + s.V.card)
        = Int.ofNat ((ideals (po_closuresystem s).toSetFamily).sum Finset.card) := by
    simp [Int.ofNat_add]
    let cio := congrArg Int.ofNat (h_sum.symm)
    simp_all only [ge_iff_le]
    --obtain ⟨val, property⟩ := x
    norm_cast

  -- 4) ideals_eq_erase による書き換え
  let iee := ideals_eq_erase s conn x mx nontriv

  -- ゴールを変形。左辺が
  -- Int.ofNat (((ideals t)).sum card) + s.V.card
  -- となるように書き換える
  have h_sum' :
       ((ideals (po_closuresystem (po_trace s x mx nontriv)).toSetFamily).sum Finset.card)
        + s.V.card
        = ((ideals (po_closuresystem s).toSetFamily).sum Finset.card) := by
    -- h_int は erase 側＋足し戻しで元に戻る等式
    symm
    exact
      Eq.symm
        (Mathlib.Tactic.Abel.subst_into_add
          ((ideals (po_closuresystem (po_trace s x mx nontriv)).toSetFamily).sum card)
          (#s.V) (((ideals (po_closuresystem s).toSetFamily).erase s.V).sum card) (#s.V)
          ((ideals (po_closuresystem s).toSetFamily).sum card)
          (congrFun (congrArg Finset.sum (iee )) card) rfl h_sum)
  -- よくわからないけど証明できた。

  have goal₁ :
      Int.ofNat ((ideals (po_closuresystem (po_trace s x mx nontriv)).toSetFamily).sum Finset.card)
        + s.V.card
        = Int.ofNat ((ideals (po_closuresystem s).toSetFamily).sum Finset.card) := by
    -- h_int は erase 側＋足し戻しで元に戻る等式
    -- dsimp [ideals] で `ideals t = (ideals s).erase s.V` を適用できる
    symm
    exact congrArg Int.ofNat (id (Eq.symm h_sum'))

  -- 最後に convert で同一視、ideals_eq_erase を使う
  dsimp [ideals] at goal₁
  convert goal₁
  simp_all only [Int.ofNat_eq_coe, Nat.cast_sum]



private lemma normalized_degree_sum_trace
  (s : Setup_po α)
  (conn  : numClasses (proj_setoid s) = 1)
  (x : s.V) (mx : po_maximal s x)
  (nontriv : s.V.card ≥ 2) :
  (po_closuresystem s).toSetFamily.normalized_degree_sum
= (po_closuresystem (po_trace s x mx nontriv)).toSetFamily.normalized_degree_sum
  + ((Int.ofNat s.V.card) - (po_closuresystem (po_trace s x mx nontriv)).number_of_hyperedges)
   :=
by
  -- 展開
  dsimp [SetFamily.normalized_degree_sum]
  -- 全体集合は必ずイデアル集合に含まれる
  have hG : s.V ∈ ideals (po_closuresystem s).toSetFamily := by
    dsimp [ideals]
    have hp : s.V ∈ s.V.powerset := by
      apply Finset.mem_powerset.mpr
      exact fun ⦃a⦄ a => a
    simp [ideals]
    let fmf := Finset.mem_filter.mpr ⟨hp, (po_closuresystem s).has_ground⟩
    simp_all only [ge_iff_le]
    obtain ⟨val, property⟩ := x
    apply And.intro
    · rfl
    · rw [mem_filter] at fmf
      simp_all only [Finset.mem_powerset, subset_refl, true_and]
  -- erase で消した分を足し戻す
  have : #(po_closuresystem (po_trace s x mx nontriv)).ground + 1=
      #(po_closuresystem s).ground := by
    dsimp [po_closuresystem]
    dsimp [po_trace]
    simp_all only [ge_iff_le, coe_mem, card_erase_of_mem]
    obtain ⟨val, property⟩ := x
    omega
  rw [←this]
  norm_cast
  have hground:#(po_closuresystem (po_trace s x mx nontriv)).ground + 1 = s.V.card :=
  by
    simp_all only
    obtain ⟨val, property⟩ := x
    rfl
  rw [←hground]
  ring_nf
  norm_cast

  let tsht := total_size_of_hyperedge_trace s conn x mx nontriv
  let nht := number_of_hyperedges_trace s conn x mx nontriv
  rw [tsht, nht]
  ring_nf

  set pn := (po_closuresystem (po_trace s x mx nontriv)).number_of_hyperedges with hpn
  set pg := ((po_closuresystem (po_trace s x mx nontriv)).ground.card : ℤ) with hpg
  rw [←hground]
  suffices h_sub : (pg + 1) * 2 + (-(pn * (pg + 1)) - (pg + 1)) = (-pn - pn * pg) + (pg + 1) from
  by
    ring_nf
    simp_all only [Nat.cast_add, Nat.cast_one, pn, pg]
    ring_nf

  simp_all only [pn, pg]
  ring

--princialIdealのtrace版。
noncomputable
def principalIdealTrace (s : Setup_po α) (x : s.V) (mx) (nontriv)
    (v : (po_trace s x mx nontriv).V) : Finset α :=
  principalIdeal (po_trace s x mx nontriv) v

/-- principalIdealTrace は単射。 現在は使ってない。-/
lemma inj_principalTrace
    (s : Setup_po α) (x mx nontriv) :
  Function.Injective (principalIdealTrace s x mx nontriv) := by
  -- 同型を `principal_injective` に帰着
  intro v w h
  apply Subtype.ext
  let pi := principal_injective (po_trace s x mx nontriv)
  exact congrArg Subtype.val (pi h)

  --simpa using principal_injective _ h

--単射性だけだと1足りないが、空集合もhyperedgeで、princialIdealではないので、成り立つ。
lemma normalized_degree_sum_lem
  (s : Setup_po α)
  --(conn  : numClasses (proj_setoid s) = 1)
  (x : s.V) (mx : po_maximal s x)
  (nontriv : s.V.card ≥ 2):
(Int.ofNat s.V.card) ≤ (po_closuresystem (po_trace s x mx nontriv)).number_of_hyperedges :=
by
  have :#(po_trace s x mx nontriv).V + 1 = Int.ofNat #s.V := by
    dsimp [po_trace]
    simp_all only [ge_iff_le, coe_mem, card_erase_of_mem]
    obtain ⟨val, property⟩ := x
    norm_cast
    omega

  rw [←this]

  let nli := nodes_le_ideals (po_trace s x mx nontriv)

  let iil2 :=isIdeal_lem2 (po_trace s x mx nontriv)

  have :(filter (fun s_1 => (po_closuresystem (po_trace s x mx nontriv)).sets s_1)) (po_trace s x mx nontriv).V.powerset =
      (filter (isIdeal (po_trace s x mx nontriv)) (po_trace s x mx nontriv).V.powerset) :=
  by
    simp_all only [Int.ofNat_eq_coe]
    obtain ⟨val, property⟩ := x
    ext a : 1
    simp_all only [mem_filter, Finset.mem_powerset, and_congr_right_iff, implies_true, iil2]

  dsimp [SetFamily.number_of_hyperedges]

  rw [←this] at nli

  exact Int.toNat_le.mp nli

--functionalMainで利用。
--traceすると、normalized_Degree_sumが減ることはない。
theorem normalized_degree_sum_gt
  (s : Setup_po α)
  (conn  : numClasses (proj_setoid s) = 1)
  (x : s.V) (mx : po_maximal s x)
  (nontriv : s.V.card ≥ 2) :
  (po_closuresystem s).toSetFamily.normalized_degree_sum
  ≤ (po_closuresystem (po_trace s x mx nontriv)).toSetFamily.normalized_degree_sum :=
by

  let ndst := normalized_degree_sum_trace s conn x mx nontriv
  rw [ndst]

  let ndsl := normalized_degree_sum_lem s x mx nontriv

  simp_all only [Int.ofNat_eq_coe, add_le_iff_nonpos_right, tsub_le_iff_right, zero_add, ge_iff_le]
  obtain ⟨val, property⟩ := x
  exact ndsl

--functionalMainで利用。
lemma trace_one_ground_card
  (s : Setup_po α)
  (x : s.V) (mx : po_maximal s x)
  (nontriv : s.V.card ≥ 2) :
  (po_closuresystem s).ground.card
  > (po_closuresystem (po_trace s x mx nontriv)).ground.card :=
by
  dsimp [po_closuresystem]
  dsimp [po_trace]
  simp_all only [ge_iff_le, coe_mem, card_erase_of_mem, gt_iff_lt, tsub_lt_self_iff, card_pos, Nat.lt_one_iff,
    pos_of_gt, and_true]
  obtain ⟨val, property⟩ := x
  exact ⟨val, property⟩
