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

    --つかってないよう。消しても良い。
    --let y : s.V := comp_po_to_sV s q (((comp_po_f s q)^[n]) x)
    -- y.val = ((comp_po_f s q)^[n] x).val としておく
    --have hy : y.val = (((comp_po_f s q)^[n]) x).val := rfl
    --simp_all only [y]
    --obtain ⟨val_1, property_1⟩ := y

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
  -- 先の constructor/rintro の証明をここに
  /-
  have xin: x.val ∈ s.V := by
    let xp := x.property
    dsimp [SetupPoComponent.comp_po_V'] at xp
    rw [Finset.mem_image] at xp
    simp at xp
    dsimp [compFinset] at xp
    simp at xp
    obtain ⟨w, hwf⟩ := xp
    exact w
  -/

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


/- 書き直したので、決して良い。

/-- `Setup_po`をひとつの連結成分に制限する関数。 -/
noncomputable def comp_po (s : Setup_po α) (q: Quotient (proj_setoid s)) : Setup_po α :=
let V' := (compFinset s q).image Subtype.val
have sub: V' ⊆ s.V := by
      simp_all only [coe_mem, V']
      rw [Finset.image_subset_iff]
      intro x a
      simp_all only [coe_mem, V']
{ V := (compFinset s q).image Subtype.val,
  po := restrict_order s q,
  nonemp := by
    -- q は連結成分なので非空
    obtain ⟨v, hv⟩ := (Quot.exists_rep q)
    refine ⟨Subtype.val v, ?_⟩
    dsimp [compFinset]
    subst hv
    simp_all only [Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists, exists_and_right,
      exists_eq_right, Subtype.coe_eta, coe_mem, exists_const]
    obtain ⟨val, property⟩ := v
    rfl

  f  := fun v' =>
    have vin : v'.val ∈ s.V := by
      exact sub v'.property
    let fv : s.V := s.f ⟨v'.val, vin⟩
        -- まず fv ∈ compFinset s q を示す
    have hq :  q = Quotient.mk (proj_setoid s) fv := by
          -- q = mk w かつ mk v' = q から，proj_max fv = proj_max v'
      obtain ⟨w, hw⟩ := Quot.exists_rep q
      calc
        q
          = Quotient.mk _ w := Eq.symm hw
        _ = Quotient.mk _ ⟨v'.1, vin⟩ := by
          -- v' が filter に拾われているので mk v' = q
          let vp := v'.property
          dsimp [compFinset] at vp
          rw [Finset.mem_image] at vp
          simp at vp
          obtain ⟨w, hwf⟩ := vp
          rename_i w_1
          subst hw
          simp_all only [V']
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
                  simp_all only [Nat.succ_eq_add_one, V']

              let pm := proj_max_unique s ⟨hmp₁, this⟩
              symm
              dsimp [fv]
              exact pm

      -- この計算全体で mk fv = q
    -- 以上で fv ∈ compFinset s q; 画像に落として Subtype 作成

    ⟨fv.1, by
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, coe_mem,
      exists_const, V', fv]
    simp [compFinset]
    rfl⟩

  order := fun x y => by
    -- unfold reach and restrict_order.le
    dsimp [reach, restrict_order]
    constructor
    · -- (→) reach f' x y なら reach s.f x.val y.val
      rintro ⟨n, h⟩
      -- h : (f'^[n]) x = y
      -- 反復の「f'^[k] x の .val = s.f^[k] x.val」を帰納で示す補題無しでいけます
      induction n with
      | zero =>
        -- iterate_zero で h : x = y, つまり x.val = y.val
        dsimp [Function.iterate_zero] at h
        subst h
        simp_all only [le_refl, V']

      | succ k ih =>
        -- h : f' (f'^[k] x) = y
        have xin:x.val ∈ s.V :=
        by
          subst h
          obtain ⟨val, property⟩ := x
          simp_all only [V']
          simp_all only [Function.iterate_succ, Function.comp_apply, V']
          exact sub property

        have yin:y.val ∈ s.V :=
        by
          subst h
          simp_all only [Function.iterate_succ, Function.comp_apply, V']
          obtain ⟨val, property⟩ := x
          simp_all only [V']
          apply sub
          simp_all only [coe_mem, V']

        dsimp [Function.iterate_succ] at h
        -- 一歩目 f (f^[k] x) = y

        injection h with _ hk
        have IH := ih hk
        -- 裏返すと s.f^[k] ↑x = ↑(f^[k] x)
        simpa [Function.iterate_succ, *] using (by
          use k + 1; exact congrArg (fun v => (v : s.V)) h)

        have : (fun v' =>
          have vin : v' ∈ s.V := by
            apply sub
            exact?
            exact sub v'.property

          ⟨s.f ⟨v',win⟩^[k] x) = y := by
            -- underlying の hn を使って
            refine congrArg (fun v' : α => ⟨v', sub _⟩) _; exact ih
              exact this
        injection h_n with _ h_k
            -- reach f (f^[k] x) y
        exact (s.order _ _).1 ⟨k+1, by
        -- defeq で h_k : f^[k] x = y をそのまま使う
          dsimp [Function.iterate_succ]; exact h_n⟩



    · -- (←) reach s.f x.val y.val なら reach f' x y
      intro hle
      obtain ⟨n, hn⟩ := (s.order _ _).2 hle
      use n
      induction n with
      | zero =>
        dsimp [Function.iterate_zero]; simp [hn]
      | succ k ih =>
        dsimp [Function.iterate_succ]
        -- f' (f'^[k] x) = mk (s.f ( (s.f^[k]) x.val ))
        -- and hn : s.f^[k+1] x.val = y.val
        -- by defeq this is exactly f'^[k+1] x = y
        congr 1
        simpa using ih

-/
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
