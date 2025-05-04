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
--import rooted.functionalTraceIdeal2
import rooted.functionalPartialTrace

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

--def classOf (s : Setup_spo α) (q : Quotient s.setoid) [DecidableEq (Quotient s.setoid)]  : Finset {x // x ∈ s.V} :=
--  Finset.filter (fun (a : {x // x ∈ s.V}) => @Quotient.mk'' _ s.setoid a = q) s.V.attach


noncomputable def compFinset (s : Setup_po α) (q : Quotient (proj_setoid s))[DecidableEq (Quotient (proj_setoid s))] : Finset {x // x ∈ s.V} :=
  Finset.filter (fun (v:{x // x ∈ s.V}) => @Quotient.mk'' _ (proj_setoid s) v = q) s.V.attach

noncomputable def restrict_order (s : Setup_po α) (q : Quotient (proj_setoid s)) : PartialOrder ((compFinset s q).image Subtype.val) :=
let V := (compFinset s q).image Subtype.val
have sub: V ⊆ s.V := by
      simp_all only [coe_mem, V]
      rw [Finset.image_subset_iff]
      intro x a
      simp_all only [coe_mem, V]
{

  le := fun (x:V) (y:V) =>

    have xin : x.val ∈ s.V := by
      simp_all only [V]
      exact sub x.property
    have yin : y.val ∈ s.V := by
      simp_all only [V]
      exact sub y.property

    s.po.le ⟨x.val,xin⟩ ⟨y.val,yin⟩

  le_refl := by
    intro a
    simp_all only [le_refl, V]

  le_antisymm := by
    intros x y hxy hyx
    have xin : x.val ∈ s.V := by
      simp_all only [coe_mem, V]
      exact sub x.property
    have yin : y.val ∈ s.V := by
      simp_all only [coe_mem, V]
      exact sub y.property
    let spl := s.po.le_antisymm ⟨x.val, xin⟩ ⟨y.val, yin⟩ hxy hyx
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    simp_all only [Subtype.mk.injEq, V]
    simpa using spl

  le_trans := by
    intros x y z hxy hyz
    have xin : x.val ∈ s.V := by
      exact sub x.property
    have yin : y.val ∈ s.V := by
      exact sub y.property
    have zin : z.val ∈ s.V := by
      exact sub z.property
    exact s.po.le_trans ⟨x.val, xin⟩ ⟨y.val, yin⟩ ⟨z.val, zin⟩ hxy hyz
}

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

namespace SetupPoComponent

variable {α : Type} [Fintype α] [DecidableEq α]

-- V' の定義をトップレベルに
private noncomputable def comp_po_V' (s : Setup_po α) (q : Quotient (proj_setoid s)) : Finset α :=
  (compFinset s q).image Subtype.val

-- V' ⊆ s.V の証明をトップレベルに
private lemma comp_po_sub (s : Setup_po α) (q : Quotient (proj_setoid s)) :
  comp_po_V' s q ⊆ s.V := by
  dsimp [comp_po_V'];
  simp [Finset.image_subset_iff]

-- 新しい遷移関数 f をトップレベルに
private noncomputable def comp_po_f
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (v' : comp_po_V' s q) : comp_po_V' s q := by
  -- ここに先の fun v' => … の本体を書く
  -- （省略）
  have vin : v'.val ∈ s.V := comp_po_sub s q v'.property

  -- 2) fv を定義
  let fv : s.V := s.f ⟨v'.val, vin⟩

  -- 3) fv が同じ連結成分にいること q = mk'' fv を示す
  have hq :  q = Quotient.mk (proj_setoid s) fv := by
          -- q = mk w かつ mk v' = q から，proj_max fv = proj_max v'
      obtain ⟨w, hw⟩ := Quot.exists_rep q
      calc
        q
          = Quotient.mk _ w := Eq.symm hw
        _ = Quotient.mk _ ⟨v'.1, vin⟩ := by
          -- v' が filter に拾われているので mk v' = q
          let vp := v'.property
          dsimp [SetupPoComponent.comp_po_V'] at vp
          rw [Finset.mem_image] at vp
          simp at vp
          obtain ⟨w, hwf⟩ := vp
          rename_i w_1
          subst hw
          dsimp [compFinset] at hwf
          rw [Finset.mem_filter] at hwf
          simp_all only [mem_attach, true_and]
          obtain ⟨val, property⟩ := w_1
          obtain ⟨val_1, property_1⟩ := v'
          obtain ⟨val_2, property_2⟩ := fv
          simp_all only
          rfl

        _ = Quotient.mk _ fv := by
          -- f preserves class: projr s fv v'
          apply Quot.sound
          dsimp [projr];
          -- proj_max s (s.f v') = proj_max s v'
          apply po_maximal_reachable_eq s ⟨v'.1, vin⟩-- (proj_max s v') (proj_max s fv)
          · constructor
            · -- reach s.f (s.f v') (proj_max s fv)
              obtain ⟨x₀, hmp, ⟨k, hk⟩⟩ := po_maximal_reachable s fv
              --dsimp [po_maximal]
              intro y hy
              have : po_maximal s (proj_max s ⟨↑v', vin⟩) :=
              by
                exact proj_max_maximal s ⟨↑v', vin⟩
              dsimp [po_maximal] at this
              specialize this y hy
              exact this

            · -- reach s.f v' (proj_max s v')
              obtain ⟨x₁, hmp₁, ⟨k, hk₁⟩⟩ := po_maximal_reachable s ⟨v'.1, vin⟩
              dsimp [reach]
              use k
              rw [hk₁]
              show  x₁ = proj_max s ⟨↑v', vin⟩
              have :reach s.f ⟨↑v', vin⟩  x₁ :=
              by
                dsimp [reach]
                use k
              let pm := proj_max_unique s ⟨hmp₁, this⟩
              symm
              exact pm
          · constructor
            · -- proj_max s (s.f v') = proj_max s v'
              obtain ⟨x₀, hmp, ⟨k, hk⟩⟩ := po_maximal_reachable s fv
              dsimp [po_maximal] at hmp
              exact proj_max_maximal s fv

            · -- reach s.f v' (proj_max s v')
              obtain ⟨x₁, hmp₁, ⟨k, hk₁⟩⟩ := po_maximal_reachable s ⟨v'.1, vin⟩
              dsimp [reach]
              use k
              rw [hk₁]
              have :reach s.f ⟨↑v', vin⟩  x₁ :=
              by
                dsimp [reach]
                use k
              have :reach s.f (s.f ⟨↑v', vin⟩)  x₁ :=
              by
                dsimp [reach]
                use k-1
                rw [←@Function.comp_apply _ _ _ s.f^[k - 1]  ]
                rw [←Function.iterate_succ]
                by_cases hk:k = 0
                case pos =>
                  rw [hk] at hk₁
                  simp at hk₁
                  rw [hk₁]
                  rw [hk ]
                  simp
                  exact (po_maximal_lem s x₁).mp hmp₁
                case neg =>
                  have : (k - 1).succ = k := by
                    exact Nat.succ_pred_eq_of_ne_zero hk
                  subst hw hk₁
                  simp_all only [Nat.succ_eq_add_one]

              let pm := proj_max_unique s ⟨hmp₁, this⟩
              symm
              dsimp [fv]
              exact pm


  -- 4) 最後に Subtype.val で要素を構築
  refine ⟨fv.1, by
    dsimp [comp_po_V']; dsimp [compFinset]
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right,
      exists_eq_right, Subtype.coe_eta, coe_mem, exists_const]
    simp [compFinset]
    rfl⟩

def comp_po_to_sV
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (v' : comp_po_V' s q) : s.V :=
⟨ v'.val, comp_po_sub s q v'.2 ⟩

-- 補題1: gⁿ x の .val が s.fⁿ と一致
private lemma comp_po_iter_val
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (x : comp_po_V' s q) :
  ∀ n : ℕ, (((comp_po_f s q)^[n]) x).val = (s.f^[n]) ⟨x, comp_po_sub s q x.2⟩ := by
  -- 先の induction/simp の証明をここに
  intro n
  induction n with
  | zero =>
    -- g^[0] x = x なので .val もそのまま x.val
    simp only [Function.iterate_zero]
    simp_all only [id_eq]
  | succ n ih =>
    -- g^[n+1] x = g (g^[n] x) なので .val を取り出し
    rw [Function.iterate_succ']
    rw [Function.iterate_succ']
    rw [Function.comp_apply]
    rw [Function.comp_apply]
    have xin: x.val ∈ s.V := by
      let xp := x.property
      dsimp [SetupPoComponent.comp_po_V'] at xp
      rw [Finset.mem_image] at xp
      simp at xp
      dsimp [compFinset] at xp
      simp at xp
      obtain ⟨w, hwf⟩ := xp
      exact w

    --使っている。ないとエラー。
    have h_eq : ((comp_po_f s q)^[n]) x = (s.f^[n] ⟨x,xin⟩).val :=
    by
      simp_all only

    obtain ⟨val, property⟩ := x
    simp_all only
    simp only [SetupPoComponent.comp_po_f, h_eq]

-- 補題2: reach g x y ↔ reach s.f sx sy
private lemma comp_po_reach_equiv
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (x y : comp_po_V' s q) :
  reach (comp_po_f s q) x y
    ↔ reach s.f ⟨x, comp_po_sub s q x.2⟩ ⟨y, comp_po_sub s q y.2⟩ :=
by

  let sx : { a // a ∈ s.V } := ⟨x, comp_po_sub s q x.2⟩
  let sy : { a // a ∈ s.V } := ⟨y , comp_po_sub s q y.2⟩
  constructor
  · -- 「comp_po_f から s.f へ」
    intro ⟨n, hn⟩; use n
    -- 反復値の取り出し補題
    have h_iter := comp_po_iter_val s q x n
    -- hn : (comp_po_f^[n] x) = y から .val を取り出す
    have h₁ : ((comp_po_f s q)^[n] x).val = y.val := congrArg Subtype.val hn
    -- これを h_iter に当てはめて s.f^[n] sx の .val = y.val
    have h₂ : (s.f^[n] sx).val = y.val := by
      rw [h_iter] at h₁; exact h₁
    -- サブタイプの等号に戻す
    apply Subtype.ext; exact h₂

  · -- 「s.f から comp_po_f へ」
    intro ⟨n, hn⟩; use n
    -- 同じく反復値の取り出し
    have h_iter := comp_po_iter_val s q x n
    -- hn : s.f^[n] sx = sy から .val を取り出す
    have h₁ : (s.f^[n] sx).val = sy.val := congrArg Subtype.val hn
    -- これを h_iter に当てはめて comp_po_f^[n] x の .val = y.val
    have h₂ : ((comp_po_f s q)^[n] x).val = y.val := by
      -- h_iter : ((comp_po_f)^[n] x).val = (s.f^[n] sx)
      rw [←h_iter] at h₁; exact h₁
    -- 最後にサブタイプの等号へ戻す
    apply Subtype.ext; exact h₂

-- 補題3: restrict_order.le の展開
@[simp]
private lemma comp_po_restrict_le_iff
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (x y : comp_po_V' s q) :
  (restrict_order s q).le x y ↔ s.po.le ⟨x, comp_po_sub s q x.2⟩ ⟨y, comp_po_sub s q y.2⟩ := by
  simp [restrict_order]

--qを除いた半順序の定義に使う部分。
private noncomputable def exclFinset
  (s : Setup_po α) (q : Quotient (proj_setoid s)) :
  Finset {x // x ∈ s.V} :=
  Finset.filter
    (fun v ↦ @Quotient.mk _ (proj_setoid s) v ≠ q)
    s.V.attach

/-- 除外部分を **`α` の `Finset`** として取り出した頂点集合 -/
private noncomputable def excl_po_V'
  (s : Setup_po α) (q : Quotient (proj_setoid s)) : Finset α :=
  (exclFinset s q).image Subtype.val

private lemma excl_po_sub (s : Setup_po α) (q) :
  excl_po_V' s q ⊆ s.V := by
  dsimp [excl_po_V', exclFinset]; simp [Finset.image_subset_iff]

end SetupPoComponent

open SetupPoComponent

-- そして comp_po 本体
noncomputable def comp_po (s : Setup_po α) (q : Quotient (proj_setoid s))
  : Setup_po α :=
{ V      := comp_po_V' s q,
  nonemp := by
    obtain ⟨v, hv⟩ := Quot.exists_rep q
    -- compFinset s q = filter (fun v => Quot.mk v = q) s.V.attach
    -- なので v ∈ compFinset s q を直接組み立てる
    have hv_mem : v ∈ compFinset s q := by
      dsimp [compFinset]
      -- フィルターの条件を満たすのが hv.symm : mk v = q
      subst hv
      simp_all only [mem_filter, mem_attach, true_and]
      obtain ⟨val, property⟩ := v
      rfl
    -- これで V' = (compFinset s q).image Subtype.val 上に v.val がある
    refine ⟨Subtype.val v, Finset.mem_image.2 ⟨v, hv_mem, rfl⟩⟩
, f      := comp_po_f s q
, po     := restrict_order s q
, order  := fun x y => by
    -- トップレベル補題をすべて利用する
    simpa [comp_po_restrict_le_iff s q, ← comp_po_reach_equiv s q x y]
      using (comp_po_reach_equiv s q x y).trans (s.order _ _) }

private noncomputable def excl_po_f
  (s : Setup_po α) (q) (v' : excl_po_V' s q) : excl_po_V' s q := by
  -- ① もとの `s.V` へ
  have hv : (v' : α) ∈ s.V := excl_po_sub s q v'.property
  let fv : s.V := s.f ⟨v', hv⟩
  let v  : s.V := ⟨v', hv⟩

  let mk : s.V → Quotient (proj_setoid s) := @Quotient.mk s.V (proj_setoid s)

  let spec_fv := proj_max_spec s fv

  -- (a) reach s.f v fv を立てる
  have reach_v_fv : reach s.f v fv := by
    -- 1 ステップで到達：f^[1] v = f v = fv
    use 1
    simp
    simp_all only [v, fv]

  -- (b) reach s.f v (proj_max s fv) を合成して得る
  have reach_v_pm : reach s.f v (proj_max s fv) := by

    -- reach.trans : reach f x y → reach f y z → reach f x z
    let rsv := reach_maximal s v--reach_v_fv spec_fv.2
    exact reach_trans s v fv (proj_max s fv) reach_v_fv rsv

  -- (c) h1 : po_maximal ∧ reach for (proj_max s fv) と v
  have h1 : po_maximal s (proj_max s fv) ∧ reach s.f v (proj_max s fv) :=
    ⟨spec_fv.1, reach_v_pm⟩

  -- (d) spec_v で得られる h2 : po_maximal s (proj_max s v) ∧ reach s.f v (proj_max s v)
  let spec_v := proj_max_spec s v

  -- (e) 同じ始点 v から両極大点に到達できるなら一意
  let eq_pm := po_maximal_reachable_eq s v (proj_max s fv) (proj_max s v) h1 spec_v

  -- (f) これで同値類不変を mk に反映
  have cls : mk fv = mk v := by
    apply Quot.sound; exact eq_pm
  -- ② 同値類が変わらないので q とは異なる
  /-
  have v_neq_q : (Quotient.mk (proj_setoid s) v) ≠ q := by
    -- v' ∈ exclFinset s q なので filter の第二条件が直接これ
    let vp := v'.property
    dsimp [SetupPoComponent.excl_po_V'] at vp
    dsimp [exclFinset] at vp
    rw [Finset.mem_image] at vp
    simp at vp
    obtain ⟨w, hwf⟩ := vp
    exact hwf

  -- ③ class preserving: mk fv = mk v
  have cls : mk fv = mk v := by
    -- 補題を取り出し
    let spec_fv := proj_max_spec s fv
    let spec_v  := proj_max_spec s v

    -- (a) fv から proj_max s fv への到達
    have reach_fv_pm : reach s.f fv (proj_max s fv) := spec_fv.2

    -- (b) v から proj_max s fv への到達
    have reach_v_pm : reach s.f v (proj_max s fv) := by
      -- reach s.f v fv  が明らかなので、それと (a) をつなぐ
      have : reach s.f v fv := by
        dsimp [reach]; use 1; simp
        exact rfl
      rcases reach_fv_pm with ⟨n, hn⟩
      dsimp [reach] at this

      rcases this with ⟨1, rfl⟩
      -- 合成して n+1 ステップで proj_max s fv に到達
      use n + 1
      calc
        (s.f^[n+1]) v
            = (s.f^[n]) (s.f v) := rfl
        _          = (s.f^[n]) fv := rfl
        _          = proj_max s fv := hn

    -- (c) x1 = proj_max s fv, x2 = proj_max s v として
    have h1 : po_maximal s (proj_max s fv) ∧ reach s.f v (proj_max s fv) := by
      exact ⟨spec_fv.1, reach_v_pm⟩

    -- (d) spec_v そのまま (po_maximal s (proj_max s v) ∧ reach s.f v (proj_max s v))
    have h2 := spec_v

    -- (e) 同じ起点 v から両方到達できるなら一意
    let pr := po_maximal_reachable_eq s v (proj_max s fv) (proj_max s v) h1 h2

    -- ここで mk fv = mk v を得る
    apply Quot.sound; exact pr

  have cls : (Quotient.mk (proj_setoid s) fv) = (Quotient.mk (proj_setoid s) v) := by
    -- projr s fv v で同値類を示す
    have pr : projr s fv v := by
      dsimp [projr]
      apply po_maximal_reachable_eq s
      -- 左：po_maximal ∧ reach (fv から proj_max s fv)
      obtain ⟨x₁, hmp₁, ⟨k₁, hk₁⟩⟩ := po_maximal_reachable s fv
      constructor
      · exact proj_max_maximal s fv
      · dsimp [reach]; use k₁;
        show s.f^[k₁] ?y = proj_max s fv
        sorry

      -- 右：po_maximal ∧ reach (v から proj_max s v)
      obtain ⟨x₂, hmp₂, ⟨k₂, hk₂⟩⟩ := po_maximal_reachable s v
      constructor
      · exact proj_max_maximal s v
      · dsimp [reach]; use k₂;
        sorry

      · simp_all only [coe_mem, not_false_eq_true, and_self, mem_attach, ne_eq]
        simp_all only [v]
        obtain ⟨val, property⟩ := v'
        obtain ⟨val_1, property_1⟩ := fv
        obtain ⟨val_2, property_2⟩ := v
        simp_all only
        tauto

    -- 以上で projr s fv v、よって
    apply Quot.sound; exact pr
  -/

  have hneq : (Quotient.mk (proj_setoid s) fv) ≠ q := by
    intro heq
    -- 仮に mk fv = q とすると mk v = q by cls
    have : (Quotient.mk _ v) = q := by calc
      _ = _ := (cls.symm)
      _ = _ := heq
    exact (v_neq_q this)

  -- ⑤ fv がフィルター後に残るので Subtype 化
  have fv_in : fv ∈ exclFinset s q := by
    dsimp [exclFinset]; simp [hneq]
  refine ⟨fv.1, by simpa [excl_po_V'] using fv_in⟩


private noncomputable def restrict_order_excl
  (s : Setup_po α) (q) :
  PartialOrder (excl_po_V' s q) :=
restrict_order_core s (excl_po_V' s q) (excl_po_sub s q)

/--
`comp_po` が「連結成分 `q` そのもの」を取るのに対し，
`excl_po` は **その成分を丸ごと取り除いた残り**で `Setup_po` を作る。
`hnonempty` は「残りが空でない」ことを仮定として与える。
-/
noncomputable def excl_po
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (hnonempty : (excl_po_V' s q).Nonempty) :
  Setup_po α :=
{ V       := excl_po_V' s q
, nonemp  := hnonempty
, f       := excl_po_f s q
, po      := restrict_order_excl s q
, order   := by
    intro x y
    -- 1) reach (excl_po_f) x y  ↔  reach s.f sx sy
    --    （sx,sy は x,y を s.V に移したもの）
    -- 2) reach s.f sx sy  ↔  s.po.le sx sy   （元の setup）
    -- 3) `restrict_order_excl` の `le` は s.po.le と同値
    --    → 以上を chain して証明
    let sx : s.V := ⟨x, excl_po_sub s q x.property⟩
    let sy : s.V := ⟨y, excl_po_sub s q y.property⟩

    -- 補題①
    have reach_equiv :
      reach (excl_po_f s q) x y ↔ reach s.f sx sy := by
      -- 反復値一致補題を `excl_po_iter_val` として同様に証明すれば
      -- `comp_po_iter_val` と同じパターンで書ける
      sorry

    -- 補題②： restrict_order_excl.le ↔ s.po.le
    have restr_iff :
      (restrict_order_excl s q).le x y ↔ s.po.le sx sy := by
      simp [restrict_order_excl]

    simpa [restr_iff] using (reach_equiv.trans (s.order sx sy)) }


/-
-- ideal 系
def IdealSys (s : Setup_po α) := partialorder_ideal_system s
def IdealComp (s : Setup_po α) (q) := partialorder_ideal_system (comp_po s q)

-- === 2. ２成分だけ取り出して DirectProduct =============================

-- 連結成分を２つ取り，証明用に名前を付ける
noncomputable def q₁ (s : Setup_po α) : Quotient (proj_setoid s) :=
  Quotient.mk (Classical.choice s.nonemp)   -- 代表をとれば一つできる

noncomputable def q₂ (s : Setup_po α) : Quotient (proj_setoid s) :=
  by
    -- 「もう一つ別のクラスがある」という前提で選択
    classical
    choose v hv using s.nonemp
    have : ∃ w, ¬projr s v w := by
      -- disconnected 仮定なら構成できる
      sorry
    exact Quotient.mk (Classical.some this)


/-- `s` から連結成分 `q` を「抹消」した半順序 -/
noncomputable
def trace_component (s : Setup_po α) (q: Quotient (proj_setoid s)) : Setup_po α :=
  po_trace s (Classical.choice (comp_po s q).nonemp)      -- ←極大点を一つ取って trace
      (by  -- その点が最大である証明
        have : po_maximal … := …
        exact this)
      (by  -- |V| ≥ 2
        have := (comp_po s q).nonemp
        simpa using … )
-/
