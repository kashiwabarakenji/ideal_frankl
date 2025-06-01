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
import rooted.functionalPartialMaximal
import rooted.functionalPartialTrace

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

-- 同値類の一つをqとして、qの側とq以外の部分に分割。
-- 片方の順序idealの大きさの和をs1、順序idealの個数をh1、頂点集合の大きさをn1とする。
-- もう片方の順序idealの大きさの和をs2、順序idealの個数をh2、頂点集合の大きさをn2とする。
-- 合わせた半順序集合に関して順序idealの大きさの和は、s1*h2+s2*h1である。
-- 合わせた半順序集合の順序idealの個数は、h1*h2である。
-- 合わせた半順序集合の台集合の大きさは、n1+n2である。
-- 平均rareであるためには、(s1*h2+s2*h1)*2-(h1*h2)*(n1+n2)<=0である。
-- それぞれが平均rareなので、s1*2-h1*n1<=0, s2*2-h2*n2<=0であることからこれはいえる。
-- 連結成分が3個以上の場合は、帰納法で証明することになる。

-- まずはcomp側でもexcl側でもない部分を定義する。

---連結成分の数。でもこれはsetoidが与えた時のもの。場所を変えたほうがいい？
def numClasses {α : Type _} (st : Setoid α)
  [Fintype α] [DecidableEq (Quotient st)] : ℕ :=
  (Finset.univ.image (Quot.mk st.r)).card

--連結成分の個数が1以上であること。
--Mainから参照あり。
lemma numClasses_pos (s : Setup_po α) :
  (numClasses (proj_setoid s)) > 0 := by
  -- numClasses の定義を展開して `Finset.card` を使う
  dsimp [numClasses]
  -- `Finset.card` の定義を展開して `Finset.nonempty` を使う
  have h1 : Fintype.card (Quotient (proj_setoid s)) ≥ 1 := by
    --apply Fintype.card_pos_iff.2
    --refine (nonempty_quotient_iff s).mpr ?_
    let qx := Quot.mk (proj_setoid s)
    obtain ⟨x, h_nonemp⟩ := Setup_po.nonemp s
    specialize qx ⟨x, h_nonemp⟩
    simp_all only [ge_iff_le]
    apply Fintype.card_pos_iff.mpr
    exact Nonempty.intro qx

  simp_all only [ge_iff_le, gt_iff_lt, card_pos, Finset.image_nonempty, attach_nonempty_iff]
  cases s
  simp_all only

--そとから参照あり。
lemma quotient_exists (s : Setup_po α) :
Nonempty (Quotient (proj_setoid s)) := by
  -- s.V.attach は空でないので同値類も空でない
  obtain ⟨v, hv⟩ := Setup_po.nonemp s
  -- `Quotient.mk` を使って同値類を作る
  let x := Quotient.mk (proj_setoid s) ⟨v, hv⟩
  use x

-- 連結成分の数。setup_poに対して、定義する。numClassesと同じだが、必要であれば復活。
--noncomputable def num_connected_components (s : Setup_po α) : ℕ :=
--  (Finset.univ.image (Quot.mk (proj_setoid s))).card
----numClasses (proj_setoid s)と定義しても良い。

--これは、comp側でもexcl側でもない？
noncomputable def  restrict_order_core
  (s : Setup_po α)
  (V' : Finset α)
  (sub : V' ⊆ s.V) :
  PartialOrder (Subtype fun x => x ∈ V') :=
{ le            := fun x y =>
    -- compare via the original order on s.V
    s.po.le ⟨x.1, sub x.2⟩ ⟨y.1, sub y.2⟩
, le_refl       := fun x =>
    -- reflexivity from the original order
    s.po.le_refl _
, le_trans      := fun {x y z} hxy hyz =>
    -- transitivity from the original order
    s.po.le_trans ⟨x.1, sub x.2⟩ ⟨y.1, sub y.2⟩ ⟨z.1, sub z.2⟩ hxy hyz
, le_antisymm  := fun {x y} hxy hyx => by
    -- antisymmetry from the original order, then Subtype.ext to lift to the subtype
    let sp := s.po.le_antisymm ⟨x.1, sub x.2⟩ ⟨y.1, sub y.2⟩ hxy hyx
    apply Subtype.ext
    simpa using sp
}
-------------------------------
---ここからcomp側の定義。
-------------------------------

-- q側の頂点集合。これをsubtype化したものがcomp_po_V'
noncomputable def compFinset (s : Setup_po α) (q : Quotient (proj_setoid s))[DecidableEq (Quotient (proj_setoid s))] : Finset {x // x ∈ s.V} :=
  Finset.filter (fun (v:{x // x ∈ s.V}) => @Quotient.mk'' _ (proj_setoid s) v = q) s.V.attach

-- q側に制限した半順序
noncomputable def  restrict_order_comp (s : Setup_po α) (q : Quotient (proj_setoid s)) : PartialOrder ((compFinset s q).image Subtype.val) :=
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



--variable {α : Type} [Fintype α] [DecidableEq α]

--まずは、comp側(qからなる側)のcomponentの準備。

-- V' の定義をトップレベルに。compFinsetをsubtype化したもの。
noncomputable def comp_po_V' (s : Setup_po α) (q : Quotient (proj_setoid s)) : Finset α :=
  (compFinset s q).image Subtype.val

-- V' ⊆ s.V の証明をトップレベルに
private lemma comp_po_sub (s : Setup_po α) (q : Quotient (proj_setoid s)) :
  comp_po_V' s q ⊆ s.V := by
  dsimp [comp_po_V'];
  simp [Finset.image_subset_iff]

-- q内に制限した新しい遷移関数 f 。
noncomputable def comp_po_f
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
          dsimp [comp_po_V'] at vp
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

--subtype化した点をs.Vに移す。
def comp_po_to_sV
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (v' : comp_po_V' s q) : s.V :=
⟨ v'.val, comp_po_sub s q v'.2 ⟩

-- 補題1: もともとのs.fと制限したcomp_po_fが一致する。
--下で使っている。
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
      dsimp [comp_po_V'] at xp
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
    simp only [comp_po_f, h_eq]

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

-- 補題3:  restrict_order_comp.le の展開。もとの半順序と制限された半順序の関係
@[simp]
private lemma comp_po_restrict_le_iff
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  (x y : comp_po_V' s q) :
  ( restrict_order_comp s q).le x y ↔ s.po.le ⟨x, comp_po_sub s q x.2⟩ ⟨y, comp_po_sub s q y.2⟩ := by
  simp [restrict_order_comp]


-- qに制限されたSetup_po の定義
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
, po     :=  restrict_order_comp s q
, order  := fun x y => by
    -- トップレベル補題をすべて利用する
    simpa [comp_po_restrict_le_iff s q, ← comp_po_reach_equiv s q x y]
      using (comp_po_reach_equiv s q x y).trans (s.order _ _) }

------------------------------
--qを除いた半順序の定義に使う部分。excl側。
-------------------------------

-- qを除いた頂点集合の定義。Subtype化したもの。
noncomputable def exclFinset
  (s : Setup_po α) (q : Quotient (proj_setoid s))[DecidableRel (projr s)]  :
  Finset {x // x ∈ s.V} :=
  Finset.filter
    (fun v ↦ @Quotient.mk _ (proj_setoid s) v ≠ q)
    s.V.attach

/-- 除外部分のFinset α の 頂点集合 -/
noncomputable def excl_po_V'
  (s : Setup_po α)
  (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)]
  [DecidableEq (Quotient (proj_setoid s))] :
  Finset α :=
  (exclFinset s q).image Subtype.val

--exclFinsetが全体の部分集合である補題。
private lemma excl_po_sub
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)]
  [DecidableEq   (Quotient (proj_setoid s))] :
  excl_po_V' s q ⊆ s.V := by
  dsimp [excl_po_V', exclFinset]
  -- Finset.image_subset_iff : image f s ⊆ t ↔ s ⊆ t.preimage f
  simp only [Finset.image_subset_iff, Subtype.coe_mk]
  intros x hx
  -- hx : x ∈ exclFinset s q
  -- exclFinset s q ⊆ s.V.attach なので x.1 ∈ s.V
  exact coe_mem x

--excl側での親の頂点を与える関数の定義。
noncomputable def excl_po_f
  (s : Setup_po α)
  (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)]
  [DecidableEq (Quotient (proj_setoid s))]
  (v' : excl_po_V' s q) :
  excl_po_V' s q := by

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

    let rsv := reach_maximal s fv--reach_v_fv spec_fv.2
    --rw [ this ]
    exact reach_trans s.f reach_v_fv rsv

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

  have v_neq_q : (Quotient.mk (proj_setoid s) v) ≠ q := by
    -- v' ∈ exclFinset s q なので filter の第二条件が直接これ
    let vp := v'.property
    dsimp [excl_po_V'] at vp
    dsimp [exclFinset] at vp
    rw [Finset.mem_image] at vp
    simp at vp
    obtain ⟨w, hwf⟩ := vp
    exact hwf

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

-- excl_po_fと通常のs.fとの関係。1 step編。
private lemma excl_po_val_step
  (s : Setup_po α) (q : Quotient (proj_setoid s))[DecidableRel (projr s)] [DecidableEq (Quotient (proj_setoid s))]
  (v : excl_po_V' s q) :
  (excl_po_f s q v).val
    = s.f ⟨v.val, excl_po_sub s q v.property⟩ := by
  -- excl_po_f は `fv : s.V := s.f ⟨v, _⟩` を作り
  -- その .val をそのまま持ってくるだけなので reflexivity
  dsimp [excl_po_f]      -- def を展開

-- 2. 制限前と後で反復値が一致する補題 n step編
private lemma excl_po_iter_val
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)] [DecidableEq (Quotient (proj_setoid s))]
  (x : excl_po_V' s q) :
  ∀ n : ℕ,
    ((excl_po_f s q)^[n] x).val
      = (s.f^[n]) ⟨x.val, excl_po_sub s q x.property⟩ := by
  intro n
  induction n with
  | zero =>
      simp [Function.iterate_zero]
  | succ n ih =>
      -- 補題を内側点 `excl_po_f x` に適用した再帰呼び出し
      --have ih' := excl_po_iter_val s q (excl_po_f s q x) n
      -- あとは反復の展開と補題を代入すれば両辺が一致
      simp [Function.iterate_succ,excl_po_val_step,ih]
      have step : (excl_po_f s q ((excl_po_f s q)^[n] x)).val
            = s.f ⟨((excl_po_f s q)^[n] x).val, excl_po_sub s q ((excl_po_f s q)^[n] x).property⟩ :=
        excl_po_val_step _ _ _

      -- 3) 帰納仮定から内部の .val の等号を取出す
      have ih_val :
        ((excl_po_f s q)^[n] x).val
          = ((s.f^[n]) ⟨x.val, excl_po_sub s q x.property⟩).val :=
      by
        simp_all only [Subtype.coe_eta]
      -- 4) calc でつなげる
      calc
        (((excl_po_f s q)^[n+1]) x).val
            = (excl_po_f s q ((excl_po_f s q)^[n] x)).val :=
        by
          rw [Function.iterate_succ']
          rw [Function.comp_apply]
        _ = s.f ⟨((excl_po_f s q)^[n] x).val, _⟩               := step
        _ = s.f ((s.f^[n]) ⟨x.val, _⟩)                         := by
          -- `congr` でサブタイプ全体を同値にしつつ内部の .val を ih_val で置換
          congr;
        _ = (s.f^[n+1]) ⟨x.val, excl_po_sub s q x.property⟩    := by
          rw [Function.iterate_succ']
          rw [Function.comp_apply]

-- exclに制限前と後でのreach の同値性
--下から参照あり。一つ下に移動する？
private lemma excl_po_reach_equiv
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)] [DecidableEq (Quotient (proj_setoid s))]
  (x y : excl_po_V' s q) :
  reach (excl_po_f s q) x y
    ↔
  reach s.f
        ⟨x.val, excl_po_sub s q x.property⟩
        ⟨y.val, excl_po_sub s q y.property⟩ := by

  -- 記号を短く
  let sx : s.V := ⟨x.val, excl_po_sub s q x.property⟩
  let sy : s.V := ⟨y.val, excl_po_sub s q y.property⟩

  constructor
  · ------------------------------------------------------------
    -- 片方向：excl_po_f → s.f
    ------------------------------------------------------------
    rintro ⟨n, hn⟩
    -- (val) に落として等式を作る
    have h_val : ((excl_po_f s q)^[n] x).val = y.val :=
      congrArg Subtype.val hn

    -- 反復値補題で置き換え
    have h_val' : (s.f^[n] sx).val = y.val := by
      simpa [excl_po_iter_val s q x n] using h_val

    -- Subtype.ext で .val = .val から等号復元
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact h_val'
  · ------------------------------------------------------------
    -- 逆方向：s.f → excl_po_f
    ------------------------------------------------------------
    rintro ⟨n, hn⟩
    -- .val = .val を取り出す
    have h_val : (s.f^[n] sx).val = sy.val :=
      congrArg Subtype.val hn

    -- 反復値補題を使って excl_po 側に戻す
    have h_val' :
        ((excl_po_f s q)^[n] x).val = y.val := by
      have := (excl_po_iter_val s q x n).symm
      simp_all only [sx, sy]

    -- Subtype.ext で復元
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact h_val'

-- functionalDirectProduct2から引用。
-- exclの頂点集合が非空でないこと。
theorem excl_po_V'_nonempty_of_classes_ge2
  (s : Setup_po α) (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)][DecidableEq (Quotient (proj_setoid s))]:
  (s.V.attach.image (Quot.mk (proj_setoid s))).card ≥ 2 →
  (excl_po_V' s q).Nonempty := by
  -- Proof details here

  intro h

  -- 同値類の集合の要素数 ≥ 2 なら 1 < card
  have h1 : 1 < (s.V.attach.image (Quot.mk (proj_setoid s))).card := by
    simpa [Nat.succ_le_iff] using h

  obtain ⟨c, hc_mem, hc_ne⟩ :=
    exists_mem_ne h1 q

  -- 以下は以前と同様
  obtain ⟨v, hv_attach, rfl⟩ := Finset.mem_image.mp hc_mem
  have v_ne : Quot.mk (proj_setoid s) v ≠ q := by simpa using hc_ne
  have hv_filter : v ∈ s.V.attach.filter fun v => Quot.mk _ v ≠ q := by
    dsimp [exclFinset]; simp [v_ne]
  have : Subtype.val v ∈ excl_po_V' s q := by
    dsimp [excl_po_V']; simp [hv_filter]
    simp_all only [ge_iff_le, mem_attach, Finset.mem_image, true_and, exists_apply_eq_apply, ne_eq, not_false_eq_true,
      mem_filter, and_self]
    obtain ⟨val, property⟩ := v
    simpa [exclFinset]
  exact ⟨v.val, this⟩

noncomputable def restrict_order_excl
  (s : Setup_po α)
  (q : Quotient (proj_setoid s))
  [DecidableRel (projr s)]
  [DecidableEq   (Quotient (proj_setoid s))] :
  PartialOrder (excl_po_V' s q) :=
restrict_order_core s (excl_po_V' s q) (excl_po_sub s q)

--excl側のSetup_poの定義。
--nonemptyの仮定は同値類が2つ以上という条件で置き換えるべき？
noncomputable def excl_po
  (s : Setup_po α) (q : Quotient (proj_setoid s))[DecidableRel (projr s)][DecidableEq (Quotient (proj_setoid s))]
  --(hnonempty : (excl_po_V' s q).Nonempty) :
  (geq2quotient: (numClasses (proj_setoid s) ≥ 2)) :
  Setup_po α :=
{ V       := excl_po_V' s q
, nonemp  := by
    have :#(Finset.image (Quot.mk ⇑(proj_setoid s)) s.V.attach) ≥ 2 := by
      dsimp [numClasses] at geq2quotient
      exact geq2quotient
    exact excl_po_V'_nonempty_of_classes_ge2 s q this
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
      exact excl_po_reach_equiv s q x y

    -- 補題②： restrict_order_excl.le ↔ s.po.le
    have restr_iff :
      (restrict_order_excl s q).le x y ↔ s.po.le sx sy := by
      simp [restrict_order_excl]
      simp_all only [sx, sy]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      obtain ⟨val_2, property_2⟩ := sx
      obtain ⟨val_3, property_3⟩ := sy
      simp_all only
      rfl

    simpa [restr_iff] using (reach_equiv.trans (s.order sx sy)) }
