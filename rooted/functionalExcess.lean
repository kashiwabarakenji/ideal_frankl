import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
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
import rooted.Parallel
import rooted.functionalCommon
--import rooted.functionalTreePreorder
import rooted.functionalTreePartialorder
import rooted.functionalSPO
import rooted.functionalSPO2
import rooted.functionalTraceIdeal


open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

------------------------------------------------------------
--次の定理は、ある同値類qがあって、(classOf s.toSetup_spo q).card ≥ 2)のときには、
--そこからxを持ってきて、traceすることにより、一つ台集合が小さくて、ndsが等しいか大きい集合族を作ることができる。
--2以上の同値類の大きさの過剰分は、1減っている。
--setup_spo2_average_rareではexcessに従って、強い帰納法で証明することになる。
--excessだけ別ファイルに独立させてもいい。functionalExcess.leanなど。定理は2つだが、closuresystemの話はしてないし。
--過剰分excessの定義
--excessは極大な同値類だけではなく、すべての同値類に対する余剰。
--excessは、Setup_spo2に対して定義されているが、Setup_spoに対しても定義できる。=>変更した。
--帰納法を使いたいのは、Setup_spo2のクラスに対してなので、Setup_spoに変更しても本当に問題がないのか？
--Setup_spoとSetup_spo2の違いを廃止するという方向性もある。
noncomputable def excess (s: Setup_spo α)  : ℕ :=
  ∑ q ∈ (Finset.univ : Finset (Quotient s.setoid)),
    ((classOf s q).card - 1)
      --traceすることで、excessはひとつ減る。

--setup_trace_spo2は、setup_traceでよさそう。(setup_trace_spo2 s x hx).toSetup_spoをsetup_traceに。
--定理の前提もSetup_spoで十分かも。
private lemma trace_excess_decrease_lem_x (s: Setup_spo α) (x: s.V) (hx: (classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2) :
 (classOfx s x).image Subtype.val = (classOf (setup_trace s x hx) (toNew s x hx (@Quotient.mk _ s.setoid x))).image Subtype.val ∪ ({x.val}:Finset α):=
by
  ext y
  apply Iff.intro
  · intro h
    rw [Finset.mem_image] at h
    simp at h
    obtain ⟨qq, hqq⟩ := h
    dsimp [classOfx] at hqq
    dsimp [classOf] at hqq
    rw [Finset.mem_filter] at hqq
    simp
    by_cases y = x.val
    case pos =>
      subst y
      simp_all only [Finset.mem_singleton, or_true, Subtype.coe_eta, Quotient.eq, Subtype.forall, mem_erase,
        ne_eq, Subtype.exists, exists_and_right, exists_eq_right, exists_const, and_true, coe_mem]
    case neg =>
      left
      have yinsV : y ∈ s.V := by
        simp_all only [ge_iff_le, mem_attach, Quotient.eq, true_and]
      have yinsV2:y ∈ (setup_trace s x hx).V :=
      by
        simp_all only [mem_attach, Quotient.eq, true_and]
        obtain ⟨val, property⟩ := x
        simp_all only
        rw [setup_trace]
        simp_all only [mem_erase, ne_eq, not_false_eq_true, and_self]
      use yinsV2
      dsimp [classOf]
      rw [Finset.mem_filter]
      have toErased_id: toErased s x hx ⟨y,yinsV⟩ = ⟨y,yinsV2⟩ := by
        dsimp [toNew]
        dsimp [toErased]
        simp_all only [mem_attach, Quotient.eq, true_and, Subtype.coe_eta]
        obtain ⟨val, property⟩ := x
        simp_all only [Subtype.mk.injEq, ↓reduceDIte]
      have equiv_yx: s.setoid.r ⟨y,yinsV⟩ x := by
        simp_all only [mem_attach, Quotient.eq, true_and]
      constructor
      · simp_all only [mem_attach, Quotient.eq, true_and]
      · dsimp [toNew]
        dsimp [toErased]
        dsimp [setup_trace]
        split
        · let rnsm := representativeNeSelf_mem_classOf s x hx
          obtain ⟨hqq1, hqq2⟩ := hqq
          let rnsm2 := representativeNeSelf_mem_classOf2 s x hx
          have : s.setoid.r (representativeNeSelf2 s x hx) x := by
            exact rnsm2
          have :s.setoid.r ⟨y,yinsV⟩ (representativeNeSelf2 s x hx):= by
            exact Setoid.trans' s.setoid equiv_yx (id (Setoid.symm' s.setoid rnsm2))

          have : (setup_trace s x hx).setoid.r (representativeNeSelf s x hx) ⟨y,yinsV2⟩ :=
          by
            --使うのは、rnsmとhqq2とtoErasedで同値なものは同値なところに移るという定理。
            dsimp [classOf]
            dsimp [setup_trace]
            dsimp [restrictedSetoid]
            exact id (Setoid.symm' s.setoid this)
          rename_i this_3
          simp_all only [mem_attach, Quotient.eq, Subtype.coe_eta]
          simp_all only
          obtain ⟨val, property⟩ := x
          simp_all only
          exact this_3
        ·
          simp_all only [mem_attach, Quotient.eq, and_self]
          simp_all only
          obtain ⟨val, property⟩ := x
          simp_all only
          exact equiv_yx

  · intro h
    rw [Finset.mem_image]
    rw [@Finset.mem_union] at h

    cases h with
    | inl h =>

      have yinsV2:y ∈ (setup_trace s x hx).V := by
        simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
        obtain ⟨w, h⟩ := h
        simp_all only
      have yinsV : y ∈ s.V := by
        exact mem_of_mem_erase yinsV2
      use ⟨y, yinsV⟩
      simp
      let rnsm2 := representativeNeSelf_mem_classOf2 s x hx
      dsimp [classOfx]
      let rnsm := representativeNeSelf_mem_classOf s x hx
      by_cases hy : y = x.val
      case pos =>
        subst hy
        simp_all only [Finset.mem_singleton, Subtype.coe_eta, Quotient.eq, Subtype.forall, mem_erase,
          ne_eq, Subtype.exists, exists_and_right, exists_eq_right, exists_const, and_true, coe_mem]
        obtain ⟨val, property⟩ := x
        dsimp [classOf] at h
        simp_all only [Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists, exists_and_right,
          exists_eq_right, exists_true_left]
        simp_all only
        exact classOf_self s ⟨val, property⟩
        --xとyが同じときは、xの同値類の大きさは、1減る。

      case neg =>
        --yはxと同じではない。
        --yは、xの同値類の中にいる。
      have :s.setoid.r ⟨y, yinsV⟩ x := by --証明に使うメインの条件は、h
        rw [Finset.mem_image] at h
        simp at h
        obtain ⟨h1, h2⟩ := h --条件はh1とh2に引き継がれる。特にh2
        --h2で、yは、xが写った先の同値類に入っていることがわかった。
        --よって、もともとのyもxと同値になる。
        let teeqx := toErased_eqx s x ⟨y, yinsV2⟩ (representativeNeSelf s x hx)
        have :(restrictedSetoid s x) ⟨y, yinsV2⟩ (representativeNeSelf s x hx) :=
        by
          --h2を使う必要あり。
          let q:= @Quotient.mk _ (setup_trace s x hx).setoid (representativeNeSelf s x hx)
          let cos := classOf_setoid (setup_trace s x hx) ⟨y, yinsV2⟩ (representativeNeSelf s x hx)

          dsimp [toNew] at h2

          have :(setup_trace s x hx).setoid = restrictedSetoid s x := by
            dsimp [setup_trace]

          rw [←this]
          rw [cos]

          have :y ∈ (setup_trace s x hx).V := by
            simp_all only

          convert h2
          dsimp [toErased]
          split
          · simp_all only [mem_erase, ne_eq, Subtype.coe_eta]
          ·
            simp_all only [mem_erase, ne_eq]
            obtain ⟨val, property⟩ := x
            simp_all only
            ext : 1
            simp_all only
            simp_all only [not_true_eq_false]

        specialize teeqx this
        exact Setoid.trans' s.setoid this rnsm2
      exact (classOf_setoid s ⟨y, yinsV⟩ x).mp this

    | inr h =>
      simp
      have : y ∈ s.V := by
        simp_all only [ge_iff_le, mem_attach, Quotient.eq, true_and]
        simp_all only [Finset.mem_singleton]
        subst h
        simp_all only [coe_mem]
      use this
      have : s.setoid.r ⟨y, this⟩ x := by
        simp_all only [ge_iff_le, Finset.mem_singleton, Subtype.coe_eta]
        subst h
        simp_all only [coe_mem]
        obtain ⟨val, property⟩ := x
        rfl
      have : x.val = y := by
        simp_all only [ge_iff_le, Finset.mem_singleton, Subtype.coe_eta]
      dsimp [classOfx]
      dsimp [classOf]
      rw [Finset.mem_filter]
      constructor
      ·
        subst this
        simp_all only [ge_iff_le, Finset.mem_singleton, Subtype.coe_eta, mem_attach]
      ·
        subst this
        simp_all only [ge_iff_le, Finset.mem_singleton, Subtype.coe_eta]

--traceすることで、excessはひとつ減る。Setup_spoの仮定でもよいかも。
--functionalMainで使われている。
theorem trace_excess_decrease (s: Setup_spo α) (x: s.V) (hx: (classOf s (@Quotient.mk _ s.setoid x)).card ≥ 2) :
  excess (setup_trace s x hx) = excess s - 1 := by
  --まずは、xを含んでいる部分の同値類が一個減るということを示す。

  --xを含まない同値類に対しては、xのtraceで不変であることを示す必要がある。
  --toErasedの写像は、xと異なる場合は、恒等写像。
--lemma toErased_eq_ne
--  (s : Setup_spo α) (x z : {x // x ∈ s.V})
--  (hx : 2 ≤ (classOf s ⟦x⟧).card)
--  (h : z ≠ x) :
--  toErased s x hx z = ⟨z.val, by
--    simp [Finset.mem_erase]
--    exact Subtype.coe_ne_coe.mpr h⟩ :=

  dsimp [excess]
  set s' := setup_trace s x hx with hs'
  --haveI := s'.toSetup_spo.spo.fintypeQuotient   -- `Finset.univ` 用の `Fintype` を入手
  --haveI := s.toSetup_spo.spo.fintypeQuotient
  let qx  : Quotient s.setoid      := ⟦x⟧
  let qx' : Quotient s'.setoid     := toNew s x hx qx
  -- 1. 右辺の和を特別クラスとその他に分割
  have hsplit_orig :
      (∑ q : Quotient s.setoid, ((classOf s q).card - 1))
      =
      (∑ q ∈ (Finset.univ.erase qx), ((classOf s q).card - 1)) +
       ((classOf s qx).card - 1) :=
  by
    let fsea := @Finset.sum_erase_add (Quotient s.setoid) _ _ _ (Finset.univ) (fun q =>  (classOf s q).card - 1) qx
    have : qx ∈ Finset.univ := by simp
    specialize fsea this
    symm
    exact fsea

  -- 2. 左辺の和を特別クラスとその他に分割
  have hsplit_new :
      ∑ q : Quotient s'.setoid , (#(classOf s' q) - 1)
      =
      ∑ q ∈ Finset.univ.erase qx' , (#(classOf s' q) - 1) +
      (#(classOf s' qx') - 1)   :=
  by
    let fsea := @Finset.sum_erase_add (Quotient s'.setoid) _ _ _ (Finset.univ) (fun q =>  (classOf s' q).card - 1) qx'
    have qxf: qx' ∈ (Finset.univ:Finset (Quotient s'.setoid)) := by simp
    specialize fsea qxf
    symm
    exact fsea

  have other_lem:∑ q ∈ Finset.univ.erase qx', (#(classOf s' q) - 1) = ∑ q ∈ Finset.univ.erase qx, (#(classOf s q) - 1):=
  by
    let S := Finset.univ.erase qx
    let T : Finset (Quotient s'.setoid) := (Finset.univ).erase qx'
    let f := fun q : Quotient s.setoid => (classOf s q).card - 1
    let g := fun q : Quotient s'.setoid => (classOf s' q).card - 1
    -- 対応写像
    let i : (q : Quotient s.setoid) → (q ∈ S) → Quotient s'.setoid :=
        fun q _ => toNew s x hx q

    -- ① 値域
    have hi :
    ∀ (q : Quotient s.setoid) (hq : q ∈ S), i q hq ∈ T := by
      intro q hq
      have hneq : q ≠ qx := (Finset.mem_erase.mp hq).left
      have hneq' : toNew s x hx q ≠ qx' := by
        intro h
        -- `toOld` で戻すと q = qx となり矛盾
        have : q = qx := by
          have := congrArg (toOld s x) h
          simpa [NewOld_id, OldNew_id, qx, qx'] using this
        exact hneq this
      have : (toNew s x hx q) ∈
            (Finset.univ : Finset (Quotient s'.setoid)) := by simp
      simpa [T, i] using Finset.mem_erase.mpr ⟨hneq', this⟩

    -- ② 関数一致（クラスサイズ）
    have heq : ∀ (q : Quotient s.setoid) (hq : q ∈ S),
        f q = g (i q hq) := by
      intro q hq
      have hq_ne : q ≠ qx := Finset.mem_erase.mp hq |>.left
      exact congrArg (fun n => n - 1) (toNew_classOf s x hx q hq_ne)

    -- ③ 単射性
    have hinj :
        ∀ (q₁ q₂ : Quotient s.setoid) (h₁ : q₁ ∈ S) (h₂ : q₂ ∈ S),
          i q₁ h₁ = i q₂ h₂ → q₁ = q₂ := by
      intros q₁ q₂ h₁ h₂ h_eq
      apply_fun toOld s x at h_eq
      rw [NewOld_id, NewOld_id] at h_eq
      exact h_eq

    have hinj2:
        ∀ (a₁ : Quotient s.setoid) (ha₁ : a₁ ∈ S) (a₂ : Quotient s.setoid) (ha₂ : a₂ ∈ S),
          i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ :=
    by
      intros q₁ q₂ h₁ h₂ h_eq
      apply_fun toOld s x at h_eq
      rw [NewOld_id, NewOld_id] at h_eq
      exact h_eq

    -- ④ 全射性
    have hsurj :
    ∀ (q' : Quotient s'.setoid), q' ∈ T →
      ∃ (q : Quotient s.setoid) (hq : q ∈ S), i q hq = q' := by
      intro q' hq'
      -- もとの代表元
      set q := toOld s x q' with hq_def
      have hq_mem : q ∈ (Finset.univ : Finset (Quotient s.setoid)) := by
        simp [hq_def]
      -- q ≠ qx を示して S へ
      have hq_ne : q ≠ qx := by
        intro h
        have hqqx: q' = qx' := by
          let ca := congrArg (toNew s x hx) h
          dsimp [q,qx] at ca
          rw [OldNew_id] at ca
          exact ca
        have : q' ∈ (Finset.univ).erase qx' := hq'
        apply Finset.mem_erase.mp this |>.left
        exact hqqx
      have hqS : q ∈ S := by
        simpa [S, hq_def] using Finset.mem_erase.mpr ⟨hq_ne, hq_mem⟩
      refine ⟨q, hqS, ?_⟩
      dsimp [i, hq_def]
      rw [hq_def]
      let on := OldNew_id s x hx q'
      exact on

    -- ⑤ 5条件そろったので sum_bij
    let fsb := Finset.sum_bij i hi hinj2 hsurj heq
    dsimp [S,T,f,g] at fsb
    symm
    exact fsb

  rw [hsplit_orig, hsplit_new]
  rw [other_lem]
  have :(#(classOf s' qx') - 1) = (#(classOf s qx) - 1) - 1 :=
  by
    let tedl :=  trace_excess_decrease_lem_x s x hx
    have xnot: x.val ∉ Finset.image Subtype.val (classOf (setup_trace s x hx) (toNew s x hx ⟦x⟧)) :=
    by
      by_contra h_contra
      rw [Finset.mem_image] at h_contra
      have :classOf (setup_trace s x hx) (toNew s x hx ⟦x⟧)⊆ (setup_trace s x hx).V.attach := by
        dsimp [classOf]
        simp_all only [Subtype.exists, exists_and_right, exists_eq_right, filter_subset, s', qx, qx']
      simp_all [s', qx, qx']
      obtain ⟨val, property⟩ := x
      obtain ⟨w, h⟩ := h_contra
      simp_all only
      simp only [setup_trace] at h
      simp only [setup_trace] at w
      simp at w
    have :(Finset.image Subtype.val (classOfx s x)).card = (Finset.image Subtype.val (classOf (setup_trace s x hx) (toNew s x hx ⟦x⟧))).card + 1:=
    by
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, not_exists,
        Finset.disjoint_singleton_right, exists_false, not_false_eq_true, card_union_of_disjoint,
        Finset.card_singleton, s', qx, qx', tedl]


    dsimp [classOf] at this
    dsimp [qx,qx']
    symm
    have h_inj1 : Set.InjOn (Subtype.val : {x // x ∈ s.V} → α)
               (↑(classOfx s x)) := by
      intro a ha b hb h
      exact Subtype.ext h

    have h_inj2 : Set.InjOn (Subtype.val : {x // x ∈ s'.V} → α)
                  (classOf s' (toNew s x hx ⟦x⟧)).toSet := by
      intro a ha b hb h
      exact Subtype.ext h

    -- この等式が前提にある：
    -- this :
    -- #(Finset.image Subtype.val (classOf s.toSetup_spo ⟦x⟧)) =
    -- #(Finset.image Subtype.val (classOf s'.toSetup_spo (toNew s.toSetup_spo x hx ⟦x⟧))) + 1

    -- image を外す

    rw [Finset.card_image_of_injOn h_inj1] at this
    let fcii := Finset.card_image_of_injOn h_inj2 --使っているっぽい。
    --dsimp [classOf] at fcii
    --dsimp [Finset.attach] at fcii
    --simp_all [s', qx, qx']
    erw [this] --謎の命令
    simp_all only [add_tsub_cancel_right]
    congr 1
    --rw [←fcii] at this

  rw [this]
  have h : 1 ≤ #(classOf s qx) - 1 := by
    have : 2 ≤ #(classOf s qx) := by
      exact hx
    exact Nat.le_sub_one_of_lt hx
  exact Eq.symm (Nat.add_sub_assoc h (∑ q ∈ Finset.univ.erase qx, (#(classOf s q) - 1)))

-- If excess is 0, all equivalence classes are 1.You might want to move this part to TraceIdeal or use the excess part to make it into one file.
--Used with functionalMain.
theorem excess_zero (s: Setup_spo α) :
  excess s = 0 → ∀ q: Quotient s.setoid, (classOf s q).card = 1 :=
by
  intro h q
  dsimp [excess] at h
  have nonneg : ∀ q, 0 ≤ (#(classOf s q) - 1) := by
    intro q
    have h_card : 1 ≤ #(classOf s q) := by
      simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, one_le_card]
      simp only [classOf_nonempty]
    exact (Nat.le_sub_one_iff_lt h_card).mpr h_card

  have sum_zero : ∑ q : Quotient s.setoid, (#(classOf s q) - 1) = 0 := h
  have all_zero : ∀ q, (#(classOf s q) - 1) = 0 := by
    simp_all only [zero_le, implies_true, sum_eq_zero_iff, Finset.mem_univ, forall_const]

  specialize all_zero q
  -- 同値類が空でないこと（カーディナリティ ≥ 1）を取得
  have h_ge : 1 ≤ #(classOf s q) := by
    simp only [classOf_nonempty, one_le_card]
  -- 減算結果が0かつ1以上 → カーディナリティ=1
  have h_le : 1 ≥ #(classOf s q) := by
    exact Nat.le_of_sub_eq_zero all_zero
  exact Eq.symm (Nat.le_antisymm h_ge h_le)

  /-

  intro h q
  have : ∀ q' :  Quotient s.setoid,0 ≤ (classOf s q').card - 1  := by
    intro q'
    simp_all only [zero_le]

  have nonneg: ∀ i ∈ Finset.univ, 0 ≤ Int.ofNat (#(classOf s i)) - 1 := by
    intro i a
    simp_all only [zero_le, implies_true, Finset.mem_univ]
    simp_all only [Int.ofNat_eq_coe, sub_nonneg, Nat.one_le_cast, one_le_card]
    simp only [classOf_nonempty]
  --let fsez := @Finset.sum_eq_zero_iff_of_nonneg _ Int _ (fun q' => (classOf s q').card - 1) (Finset.univ : Finset (Quotient s.setoid)) nonneg
  let fsez :=
      @Finset.sum_eq_zero_iff_of_nonneg
        (Quotient s.setoid)  -- α
        ℤ                    -- β
        _                    -- DecidableEq
        _                    -- OrderedCancelAddCommMonoid
        _
        (fun q => Int.ofNat ((classOf s q).card) - 1) -- f
        (Finset.univ : Finset (Quotient s.setoid))    -- s
        nonneg                -- hf

  --let con := classOf_nonempty s.toSetup_spo q
  dsimp [excess] at h
  have :∀ i ∈ Finset.univ, (fun q' => Int.ofNat (#(classOf s q')) - 1) i = 0 :=
  by
    intro i a
    simp_all only [Finset.mem_univ, Int.ofNat_zero, Int.ofNat_one, Int.ofNat_sub]
    apply fsez.mp
    simp
    have h_cast :
      (∑ q : Quotient s.setoid, (Int.ofNat (#(classOf s q)) - 1 : ℤ))
        =
      Int.ofNat (∑ q : Quotient s.setoid, (#(classOf s q) - 1)) :=
    by
      simp [Int.cast_sum]  -- ℕ の和を ℤ にキャスト
      let fssd := @Finset.sum_sub_distrib _ _ (Finset.univ : Finset (Quotient s.setoid)) (fun q' => Int.ofNat (#(classOf s q'))) (fun q' => 1) _
      suffices (∑ x : Quotient s.setoid, Int.ofNat (#(classOf s x))) - Int.ofNat (Fintype.card (Quotient s.setoid)) =
      ∑ x : Quotient s.setoid,   (Int.ofNat (#(classOf s x)) - 1) from by

        have :∀ q':Quotient s.setoid, Int.ofNat ((#(classOf s q')) - 1) = Int.ofNat (#(classOf s q')) - 1 := by
          intro q'
          simp [Int.ofNat_sub]
          have h_card_ge : 1 ≤ #(classOf s q') := by
            specialize nonneg q' (Finset.mem_univ _)
            -- 0 ≤ ↑n - 1 ⇒ n ≥ 1
            -- Int.ofNat n - 1 ≥ 0 ⇒ Int.ofNat n ≥ 1 ⇒ n ≥ 1
            simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true, Int.ofNat_eq_coe,
              sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, sub_nonneg, Nat.one_le_cast, one_le_card]

          rw [Nat.cast_sub  h_card_ge] --(#(classOf s.toSetup_spo q')) 1
          simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true, Int.ofNat_eq_coe,
            sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, one_le_card, Nat.cast_one]

        simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true, Int.ofNat_eq_coe,
          CharP.cast_eq_zero, sum_const_zero]
        --intro i_1
        simp_all only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
        --goal ∑ x, ↑(#(classOf s x)) - ↑(Fintype.card (Quotient s.setoid)) = 0
        rw [this]
        · have : ((∑ x : Quotient s.setoid, (Int.ofNat (#(classOf s x)))) -
                  Int.ofNat (Fintype.card (Quotient s.setoid)))
                  =
                  (∑ x : Quotient s.setoid, (Int.ofNat (#(classOf s x)) - 1 : ℤ)) :=
          by
            -- 1. 左辺を「和 － 定数和」の形に直す
            have h₁ :
                (∑ x : Quotient s.setoid, (Int.ofNat (#(classOf s x)))) -
                Int.ofNat (Fintype.card (Quotient s.setoid))
                =
                (∑ x : Quotient s.setoid, (Int.ofNat (#(classOf s x)))) -
                (∑ x : Quotient s.setoid, (1 : ℤ)) := by
              -- `sum_const` で 1 の和がカードと一致
              simp [sum_const, card_univ]

            -- 2. `sum_sub_distrib` で Σ(a) − Σ(b) = Σ(a − b)
            have h₂ :
                (∑ x : Quotient s.setoid, (Int.ofNat (#(classOf s x)))) -
                (∑ x : Quotient s.setoid, (1 : ℤ))
                =
                ∑ x : Quotient s.setoid,
                  ((Int.ofNat (#(classOf s x))) - (1 : ℤ)) := by
                    simp_all only [Int.ofNat_eq_coe, sum_const, card_univ, nsmul_eq_mul, mul_one, sum_sub_distrib]
            -- 3. ゴールは h₁ ⬝ h₂
            simp_all only [Int.ofNat_eq_coe, sum_const, card_univ, nsmul_eq_mul, mul_one, sum_sub_distrib]
          -- this:  ∑ x, Int.ofNat #(classOf s x) - Int.ofNat (Fintype.card (Quotient s.setoid)) = ∑ x, (Int.ofNat #(classOf s x) - 1)
          -- goal:  ∑ x, ↑(#(classOf s x)) - ↑(Fintype.card (Quotient s.setoid)) = ↑(#(classOf s ?m.72187)) - 1
          sorry


        · exact q
      rw [fssd]
      simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true, Int.ofNat_eq_coe, sum_const,
        card_univ, nsmul_eq_mul, mul_one]
    simp_all

    simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true]

  let ts := this q
  have :q ∈ Finset.univ := by
    exact Finset.mem_univ q
  specialize ts this
  simp at ts
  have h_eq : Int.ofNat (#(classOf s q)) - 1 + 1= 1 := by
    simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true, Int.ofNat_eq_coe, zero_add]
  simp at h_eq
  simp_all only [sum_eq_zero_iff, Finset.mem_univ, forall_const, le_refl, implies_true, Int.ofNat_eq_coe, Nat.cast_one,
    sub_self]
-/

--excessが正ならば、大きさ2以上の同値類が存在。
--この補題もSetup_spo2の前提でなくても成り立ちそう。大きさが2以上の同値類がMaximalであることは、Setup_spo2の前提が必要だが、ここではそこまでいってない。
--functionalMainで使っている。
theorem exists_q_card_ge_two_of_excess_pos {α : Type} [Fintype α] [DecidableEq α] (s : Setup_spo α)
  (h : excess s > 0) :
  ∃ q : Quotient s.setoid, (classOf s q).card ≥ 2 := by
  -- 対偶法で示す
  by_contra h'
  -- もし ∀ q, (classOf q).card < 2 ならば各項 (card - 1) = 0 で和も 0 になる
  have hz : excess s = 0 := by
    dsimp [excess]
    have zero_terms : ∀ q, (classOf s q).card - 1 = 0 := by
      intro q
      -- ¬ ∃ q, card ≥ 2 から ¬ (card ≥ 2) をまず得て，Nat.not_le.mp で card < 2 に，
      -- さらに Nat.lt_succ_iff.mp で card ≤ 1 にし，Nat.sub_eq_zero_of_le で m - 1 = 0 を結論
      apply Nat.sub_eq_zero_of_le
      apply Nat.lt_succ_iff.mp
      apply Nat.not_le.mp
      exact not_exists.mp h' q
    simp [zero_terms]
  -- しかし h : excess s > 0 と矛盾
  exact (Nat.ne_of_gt h) hz
