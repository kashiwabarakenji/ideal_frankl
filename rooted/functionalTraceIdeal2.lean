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
--import rooted.Parallel
import rooted.functionalCommon
import rooted.functionalTreePartialorder
import rooted.functionalSPO
import rooted.functionalSPO2
import rooted.functionalTreeIdeal
import rooted.functionalIdealrare
import rooted.functionalTraceIdeal

open Finset Set Classical

--半順序の構造Setup_poとの橋渡しの部分。
--同値類の大きさが全部1であれば、Setup_poとみなせるということを示すのがメイン。
--前半のexcessの部分は、excessが0であれば同値類の大きさが全部1という形で繋がっている。
--前半部分はファイル名をfunctionalEqualOneなどに変えて独立させるか、TraceIdealに移動してもよい。
--ただし、ここにあるのは、excessを利用した議論もある。
--とりあえず、後半にはclosuresystemも出てくるのでそのまま。
--いまところ、
--TraceIdeal Idealに関係があって、excesが出てこないもの。
--functionalExcess Excessが出てくるもの。
--functionalSetuppo Setup_soに帰着させる部分。
--に再編成するとよいかも。

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

--excessが0であれば、同値類の大きさがすべて1。この部分は、TraceIdealに移動するか、excessの部分でまとめて1ファイルにするといいかも。
--functionalMainで使っている。
theorem excess_zero (s: Setup_spo α) :
  excess s = 0 → ∀ q: Quotient s.setoid, (classOf s q).card = 1 :=
by
  intro h q
  have : ∀ q' :  Quotient s.setoid,0 ≤ (classOf s q').card - 1  := by
    intro q'
    simp_all only [zero_le]

  have nonneg: ∀ i ∈ Finset.univ, 0 ≤ Int.ofNat (#(classOf s i)) - 1 := by
    intro i a
    simp_all only [zero_le, implies_true, Finset.mem_univ]
    simp_all only [Int.ofNat_eq_coe, sub_nonneg, Nat.one_le_cast, one_le_card]
    simp only [classOf_nonempty]
  let fsez := @Finset.sum_eq_zero_iff_of_nonneg _ Int _ (fun q' => (classOf s q').card - 1) (Finset.univ : Finset (Quotient s.setoid)) nonneg
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
        intro i_1
        simp_all only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
        rw [this]
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

-----------------------------------------------------------
--trace_parallel_average_rare を使って大きさ2以上の同値類の頂点をtraceすると、normalized degree sumが下がらないことを証明する。
--一般的な枠組みでは、trace_parallel_average_rareで証明済み。
--spo2_rareを利用しているので、仮定はSetup_spoでなくて、Setup_spo2である必要がある。
--下のtrace_ideal_nds_increase2で、setup_traceを利用する形に書き換え。
--以下の議論は、excessに関係がないので、TraceIdealに移動してもよい。
lemma trace_ideal_nds_increase (s: Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x
)).card ≥ 2) :
  (spo_closuresystem s.toSetup_spo).normalized_degree_sum ≤ ((spo_closuresystem s.toSetup_spo).toSetFamily.trace x.val (by simp_all only [ge_iff_le,
    coe_mem] ) (by
  have :s.V = (spo_closuresystem s.toSetup_spo).ground := by
    simp_all only [ge_iff_le]
    obtain ⟨val, property⟩ := x
    rfl
  have : s.V.card ≥ 2:= by
    let csl := card_subtype_le_original  (classOf s.toSetup_spo ⟦x⟧)
    linarith
  exact this
    )).normalized_degree_sum :=
by
  have : s.V.card = (spo_closuresystem s.toSetup_spo).ground.card := by
    simp_all only [ge_iff_le]
    obtain ⟨val, property⟩ := x
    rfl

  let tpar := trace_parallel_average_rare (spo_closuresystem s.toSetup_spo) x (by simp_all only [ge_iff_le, coe_mem])
  have :∃ y, ↑x ≠ y ∧ parallel (spo_closuresystem s.toSetup_spo) (↑x) y :=
  by
    let xx := representativeNeSelf2 s.toSetup_spo x hx
    use xx
    constructor
    · dsimp [xx]
      dsimp [representativeNeSelf2]
      have rprop : (representativeNeSelf s.toSetup_spo x hx).val ∈ s.V.erase x.val := by
        exact coe_mem (representativeNeSelf s.toSetup_spo x hx)
      rw [Finset.mem_erase] at rprop
      exact rprop.1.symm
    · dsimp [xx]
      dsimp [representativeNeSelf2]
      have :s.setoid (representativeNeSelf2 s.toSetup_spo x hx) x := by
        exact representativeNeSelf_mem_classOf3 s.toSetup_spo x hx
      have :s.setoid x (representativeNeSelf2 s.toSetup_spo x hx) := by
        exact id (Setoid.symm' s.setoid this)
      let sce := spo_closuresystem_equiv2 s.toSetup_spo x (representativeNeSelf2 s.toSetup_spo x hx) this
      have :x ≠ representativeNeSelf2 s.toSetup_spo x hx := by
        dsimp [representativeNeSelf2]
        have rprop : (representativeNeSelf s.toSetup_spo x hx).val ∈ s.V.erase x.val := by
          exact coe_mem (representativeNeSelf s.toSetup_spo x hx)
        rw [Finset.mem_erase] at rprop
        let rp1s := rprop.1.symm
        exact fun a => rp1s (congrArg Subtype.val a)
      have : parallel (spo_closuresystem s.toSetup_spo) ↑x ↑(representativeNeSelf2 s.toSetup_spo x hx) :=
      by
        simp at sce
        cases sce
        case inr h =>
          exact False.elim (this h)
        case inl h =>
          exact h
      exact this

      --parallelとsetoidの関係
  specialize tpar this
  have : (spo_closuresystem s.toSetup_spo).is_rare ↑x :=
  by
    exact spo2_rare s ⟦x⟧ hx x rfl
  specialize tpar this
  exact tpar

--trace_ideal_nds_increaseよりはすっきりした形。setup_traceを利用している。仮定はSetup_spo2である必要。
--Mainのh_ndsを証明するときに使っている。
theorem trace_ideal_nds_increase2 (s: Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x
)).card ≥ 2) :
(spo_closuresystem s.toSetup_spo).normalized_degree_sum ≤ (spo_closuresystem (setup_trace s.toSetup_spo x hx)).normalized_degree_sum :=
by
  let tin := trace_ideal_nds s.toSetup_spo x hx
  simp
  rw [tin]
  exact trace_ideal_nds_increase s x hx

--------------------------------------------------------
--- ここから先は、traceとは関係ない内容か。
-------------------------------------------------------------

  --ただのSetupと比較するとシンプルになっている。preorderのときのような同値類を考える必要がない。
  --これは、次の枠組みの話なのでPartialMaximalに移動してもよい。
structure Setup_po (α : Type) [Fintype α] [DecidableEq α] where
(V : Finset α)
(nonemp   : V.Nonempty)
(f : V → V)
(po : PartialOrder V)
(order : ∀ x y : V, (reach f x y ↔ po.le x y)) --fからpo.leが決まる。

--idealsystemとclosure systemの名称でどちらがいいか。定義名は、po_closuresystemという手もある。
def po_closuresystem {α : Type} [Fintype α] [DecidableEq α] (s: Setup_po α) : ClosureSystem α :=
{ ground := s.V,
  sets := fun ss : Finset α => ss ⊆ s.V ∧(∀ v : s.V, v.val ∈ ss → (∀ w : s.V, s.po.le w v → w.val ∈ ss)),
  inc_ground := by
    intro ss a
    exact a.1,
  has_ground := by
    simp
  nonempty_ground := by
    exact s.nonemp,
  intersection_closed := by
    intro s_1 t a a_1
    simp_all only [Subtype.forall, Finset.mem_inter, and_imp]
    obtain ⟨left, right⟩ := a
    obtain ⟨left_1, right_1⟩ := a_1
    apply And.intro
    · intro x hx
      simp_all only [Finset.mem_inter]
      obtain ⟨left_2, right_2⟩ := hx
      apply left left_2
    · intro a b a_1 a_2 a_3 b_1 a_4
      apply And.intro
      · tauto
      · tauto
}

--同値類の大きさが全部1のSetup_poに対して、対応するSetup_poを定義することができる。
--そして、idealの集合族が一致する。

--次の定義に利用。補題には、Setup_poは出てこない。ただ、同値類の個数が1という制約が特殊なので、ここでよいかも。
lemma class_size_one_implies_eq (s: Setup_spo α) (x y: s.V) (ssl  : (⟦x⟧ : Quotient s.setoid) = ⟦y⟧) (hq1x :#(Finset.filter (fun a => @Quotient.mk'' _ s.setoid a = ⟦x⟧) s.V.attach) = 1) (hq1y :#(Finset.filter (fun a => @Quotient.mk'' _ s.setoid a = ⟦y⟧) s.V.attach) = 1) :
     (x : α) = y := by
  -- 同値類 `{ a | ⟦a⟧ = ⟦x⟧ }` のカードが 1 → その唯一元を取り出す
  have hcard :=
    (Finset.card_eq_one.mp hq1x)   -- ⟨z, hz_mem, huniq⟩
  --rcases hcard with ⟨z, hz_mem, huniq⟩
  obtain ⟨xx, hxx_mem⟩ := hcard

  -- `x` がその Finset に入っていることは自明
  have hx_mem :
      (x : {a // a ∈ s.V}) ∈ Finset.filter (fun a => @Quotient.mk'' _ s.setoid a = ⟦x⟧) s.V.attach := by
    -- `Quotient.mk'' x = ⟦x⟧` なので `simp`
    rw [Finset.mem_filter]
    simp_all only [Quotient.eq, mem_attach, and_self]


  -- `y` も `ssl : ⟦x⟧ = ⟦y⟧` から同じ Finset に入る
  have hy_mem :
      (y : {a // a ∈ s.V}) ∈ Finset.filter (fun a => @Quotient.mk'' _ s.setoid a = ⟦x⟧) s.V.attach := by
    rw [Finset.mem_filter]
    simp_all only [Quotient.eq, mem_attach, and_self]
    exact ⟨trivial, id (Setoid.symm' s.setoid ssl)⟩
  -- 「唯一性」より `x = z` と `y = z`
  have heq: xx = x := by
    simp_all only [Quotient.eq, Finset.mem_singleton, mem_filter, mem_attach, true_and]
  have : xx = y := by
    subst heq
    simp_all only [Quotient.eq, Finset.mem_singleton]
  subst heq this
  simp_all only [Quotient.eq, Finset.mem_singleton, Finset.card_singleton]

--traceを撮った時の半順序の定義。
noncomputable def po_ideal_system_from_allone_le {α : Type} [Fintype α] [DecidableEq α] (s: Setup_spo α)  (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1): PartialOrder s.V :=
{
  le := fun (x y:s.V) => s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y),

  le_refl := by
    intro x
    exact s.spo.le_refl (@Quotient.mk s.V s.setoid x),

  le_trans := by
    intros x y z hxy hyz
    have sxy: s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) := by
      exact hxy
    have syz: s.spo.le (@Quotient.mk s.V s.setoid y) (@Quotient.mk s.V s.setoid z) := by
      exact hyz
    have sxz: s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid z) := by
      exact s.spo.le_trans (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) (@Quotient.mk s.V s.setoid z) sxy syz
    exact sxz,

  le_antisymm := by
    intros x y hxy hyx
    have sxy: s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) := by
      exact hxy
    have syx: s.spo.le (@Quotient.mk s.V s.setoid y) (@Quotient.mk s.V s.setoid x) := by
      exact hyx
    let ssl := s.spo.le_antisymm (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) sxy syx
    dsimp [classOf] at hq1
    let hq1x := hq1 (@Quotient.mk s.V s.setoid x)
    let hq1y := hq1 (@Quotient.mk s.V s.setoid y)

    let csoi := class_size_one_implies_eq s x y ssl hq1x hq1y
    exact Subtype.eq csoi
}

--hq1が成り立つ時は、同値類と要素が全単射が存在して、お互いのreachが対応していることも示すか。
--最終的には大小関係が対応していることを示す。

-- 同値類の大きさが1のときに関する補題。
lemma equal_one (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) (x y: s.V) :
  (@Quotient.mk s.V s.setoid x) = (@Quotient.mk s.V s.setoid y) ↔ x = y := by
  constructor
  · intro h
    -- 1. 「x の同値類」は要素数 1．唯一の要素を取り出す
    have hcard := hq1 ⟦x⟧
    --rcases Finset.card_eq_one.mp hcard with
    obtain ⟨z, hz_mem⟩ := Finset.card_eq_one.mp hcard
    -- 2. まず `x` 自身がその Finset に入る
    have hx_mem : (x : {a // a ∈ s.V}) ∈ classOf s ⟦x⟧ := by
      exact classOf_self s x
    -- 3. `y` も `hq_eq` により同じ同値類へ入る
    have hy_mem :
        (y : {a // a ∈ s.V}) ∈ classOf s ⟦x⟧ :=
    by
      -- `simp` へ渡すために `hq_eq` で書き換え
      have : (Quotient.mk'' y : Quotient s.setoid) = ⟦x⟧ := by
        exact id (Eq.symm h)
      simp [classOf, this]           -- membership registered
      simp_all only [Finset.card_singleton, Finset.mem_singleton, Quotient.eq]
    -- 4. 同値類の要素は 1 つしかないので両者は等しい
    have hxz : (x : {a // a ∈ s.V}) = z := by simp_all only [Quotient.eq, Finset.card_singleton, Finset.mem_singleton] --huniq _ hx_mem
    have hyz : (y : {a // a ∈ s.V}) = z := by
      subst hxz
      simp_all only [Quotient.eq, Finset.card_singleton, Finset.mem_singleton] --huniq _ hy_mem
    -- 5. 結果として x = y
    subst hyz hxz
    simp_all only [Finset.card_singleton, Finset.mem_singleton]
  · intro h
    subst h
    simp_all only

-- 同値類の大きさが1のときに関する補題。
lemma equal_one2 (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) (x: s.V) :
   (@Quotient.mk _ s.setoid x).out = x :=
by
  let q : Quotient s.setoid := ⟦x⟧

  -- 1. その同値類の Finset はサイズ 1
  have hcard : (classOf s q).card = 1 := hq1 q
  --rcases (Finset.card_eq_one.mp hcard) with
  obtain ⟨z, hz_mem⟩ := Finset.card_eq_one.mp hcard

  -- 2. `x` 自身は必ずその Finset に入る
  have hx_mem : (x : {a // a ∈ s.V}) ∈ classOf s q := by
    unfold classOf q
    simp [q]
    simp_all [q]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := z
    rfl

  -- 3. `(⟦x⟧.out)` も同じ同値類に属するので Finset に入る
  have hout_mem :
      ((@Quotient.mk _ s.setoid x).out) ∈ classOf s q := by
    -- (a) 属していること
    have hout_inV :
        ((@Quotient.mk _ s.setoid x).out) ∈ s.V.attach :=
    by
      simp_all only [Finset.mem_singleton, mem_attach, q]
    -- (b) `Quotient.mk'' out = ⟦x⟧`
    have hquot :
        (Quotient.mk'' ((@Quotient.mk _ s.setoid x).out)
          : Quotient s.setoid) = q := by
      -- `Quotient.out_eq` : `Quotient.mk'' (out q') = q'`
      have : (Quotient.mk'' ((@Quotient.mk _ s.setoid x).out)
                : Quotient s.setoid)
              = (@Quotient.mk _ s.setoid x) :=
      by
        simp_all only [Finset.mem_singleton, mem_attach, Quotient.out_eq, q]


      simp_all only [Finset.mem_singleton, mem_attach, Quotient.out_eq, q]
    -- (c) まとめて membership
    unfold classOf q
    simp [hout_inV, hquot]
    exact (@Quotient.eq _ s.setoid ⟦x⟧.out x).mp hquot

  -- 4. 要素が 1 つだけ ⇒ `x = z` かつ `out = z`
  have hxz  : (x : {a // a ∈ s.V}) = z :=
  by
    simp_all only [Finset.mem_singleton, q]
  have houtz : ((@Quotient.mk _ s.setoid x).out) = z :=
  by
    subst hxz
    simp_all only [Finset.mem_singleton, q]

  -- 5. 連鎖して `out = x`
  subst hxz
  simp_all only [q]

--同値類の大きさが1のときに関する補題。
lemma equal_one_f (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) (x y: s.V) :
  s.fq (@Quotient.mk s.V s.setoid x) = (@Quotient.mk s.V s.setoid y) ↔ ((fun xx => s.fq (@Quotient.mk _ s.setoid xx)) x).out = y :=
by
  have h_eq₁ := equal_one s hq1 ((s.fq ⟦x⟧).out) y
  -- 方向 ⇒
  constructor
  · intro hq               -- 仮定: `s.fq ⟦x⟧ = ⟦y⟧`
    -- `Quotient.mk''` で両辺を代表元に戻す
    have : (Quotient.mk'' (s.fq ⟦x⟧).out : Quotient s.setoid) =
            (s.fq ⟦x⟧) := by
      simp_all only [Quotient.out_eq, true_iff]
    -- 代表元の等式を組み合わせて `⟦out⟧ = ⟦y⟧`
    have hq' : (Quotient.mk'' (s.fq ⟦x⟧).out : Quotient s.setoid) = ⟦y⟧ := by
      simpa [this] using hq
    -- `equal_one` で要素の等式へ
    have : (s.fq ⟦x⟧).out = (y : α) :=
    by
      simp_all only [Quotient.out_eq, true_iff]
    simp_all only [Quotient.out_eq, true_iff]
  -- 方向 ⇐
  · intro hout               -- 仮定: `(s.fq ⟦x⟧).out = y`
    -- `equal_one` の «←» 方向
    have hout_q :
        (Quotient.mk'' (s.fq ⟦x⟧).out : Quotient s.setoid)
          = (⟦y⟧ : Quotient s.setoid) := by
      exact (h_eq₁.mpr hout)
    -- 代表元と `Quotient.out_eq` で `s.fq ⟦x⟧ = ⟦y⟧`
    have : (Quotient.mk'' (s.fq ⟦x⟧).out : Quotient s.setoid)
            = s.fq ⟦x⟧ :=
    by
      subst hout
      simp_all only [Quotient.out_eq]
    simpa [this] using hout_q

--同値類の大きさが1のときに関する補題。
lemma equal_one_setroid (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) (x y: s.V) :
  s.setoid x y ↔ x = y :=
by
  let eo := equal_one s hq1 x y
  constructor
  · intro h
    have : s.setoid x y := by
      exact h
    have : x = y := by
      rw [←Quotient.eq] at this
      exact (equal_one s hq1 x y).mp this
    exact this
  · intro h
    subst h
    exact (@Quotient.eq _ s.setoid x x).mp rfl

--同値類の大きさが1のときに関する補題。
lemma po_ideal_system_from_allone_lem (α : Type) [Fintype α] [DecidableEq α] (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) (x y : s.V)(n:Nat):
 s.fq^[n] (@Quotient.mk s.V s.setoid x) = (@Quotient.mk s.V s.setoid y) ↔ (fun x => (s.fq ⟦x⟧).out)^[n] x = y:=
by
  -- `g` は `(s.fq ⟦·⟧).out`
  let g : s.V → s.V := fun xx => (s.fq ⟦xx⟧).out
  -- 帰納法 on `n`
  induction n generalizing x y with
  | zero =>
      -- 0 回の反復は恒等
      simp [Function.iterate_zero, g]
      -- `Quotient.mk` も `out` も恒等に化ける
      have h := equal_one_f s hq1 x x
      simp [g] at h
      exact equal_one_setroid s hq1 x y
  | succ k ih =>
      -- 反復の再帰展開
      show
        s.fq^[k.succ] ⟦x⟧ = ⟦y⟧
          ↔ (g^[k.succ]) x = y
      -- `iterate_succ'` : f^[n+1] = f ∘ f^[n]
      rw [Function.iterate_succ']
      rw [Function.iterate_succ']
      --simp [g] at *
      -- 記号整理
      set zq  := s.fq^[k] ⟦x⟧ with hzq
      set z   := (g^[k]) x     with hz
      -- 帰納仮定を zq,z へ適用

      have ih' := (ih x z).trans (by
        -- ih : fq^[k] ⟦x⟧ = ⟦z⟧ ↔ g^[k] x = z
        -- rewrite hzq hz to `zq = ...`, `z = ...`
        simp_all only [Subtype.coe_eta, true_iff, g, zq, z]
        assumption
        )

      -- `equal_one_f` で 1 段ぶん
      have step :=
        (equal_one_f s hq1 (x := z) (y := y)).symm
      -- 結合

      constructor
      · intro h
        have : zq = @Quotient.mk _ s.setoid z := by
          simp_all only [Subtype.forall, Subtype.coe_eta, Function.comp_apply, zq, g, z]
        simp
        simp at h
        rw [←hz]
        dsimp [g]
        rw [←hzq] at h
        rw [this] at h
        exact (equal_one_f s hq1 z y).mp h
      · intro h
        -- `g^[k]` の定義を展開
        have : g^[k] x = z := by
          simp [g, hz]

        -- `s.fq` の定義を展開
        have : s.fq ⟦z⟧ = ⟦y⟧ := by
          apply step.mp
          simp
          subst h
          simp_all only [Subtype.forall, Subtype.coe_eta, Function.comp_apply, Quotient.out_eq, zq, g, z]

        -- `equal_one_f` で 1 段ぶん
        have : (Quotient.mk'' (s.fq ⟦z⟧).out : Quotient s.setoid) = ⟦y⟧ := by
          simp_all only [Quotient.out_eq, true_iff]
        -- `equal_one` で要素の等式へ
        have : (s.fq ⟦z⟧).out = y := by
          simp_all only [Quotient.out_eq, true_iff]
        -- 結合して完了

        let eos := equal_one_setroid s hq1 z y
        let eof := (equal_one_f s hq1 z y).mpr
        --dsimp [z] at eof
        rename_i this_2 this_3
        rw [←this_2]
        have : zq = @Quotient.mk _ s.setoid z := by
          subst h
          simp_all only [Subtype.coe_eta, Quotient.out_eq, zq, z, g]
        exact congrArg s.fq this

--すべての同値類の大きさが1のときに関して、対応するSetup_poを定義する。メインで使っている。
noncomputable def po_ideal_system_from_allone {α : Type} [Fintype α] [DecidableEq α] (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1): Setup_po α :=
{
  V := s.V,
  nonemp := by
    exact s.nonemp,
  f := fun x => Quotient.out (s.fq (@Quotient.mk _ s.setoid x)),
  po := po_ideal_system_from_allone_le s hq1,
  order := by
    intro x y
    dsimp [po_ideal_system_from_allone_le]
    constructor
    · intro hxy
      have :s.spo.le (@Quotient.mk s.V s.setoid x) (s.fq (@Quotient.mk s.V s.setoid x)) := by
        apply reach_leq s (@Quotient.mk s.V s.setoid x) (s.fq (@Quotient.mk s.V s.setoid x))
        dsimp [reach]
        use 1
        simp

      have goal: s.spo.le (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y) := by
        apply reach_leq s (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y)
        -- Add the necessary proof here
        dsimp [reach]
        dsimp [reach] at hxy
        obtain ⟨n,hnl⟩ := hxy
        use n
        exact (po_ideal_system_from_allone_lem α s hq1 x y n).mpr hnl
      --have : Quotient.out (s.fq (@Quotient.mk _ s.setoid x)) = Quotient.out (s.fq (@Quotient.mk _ s.setoid y)) := by
      --  sorry
      exact goal

    · intro hxy
      let rlr := reach_leq_rev s (@Quotient.mk s.V s.setoid x) (@Quotient.mk s.V s.setoid y)
      specialize rlr hxy
      show reach (fun x => (s.fq ⟦x⟧).out) x y
      --fとfqの対応がreachの対応になる。補題が必要。
      dsimp [reach]
      dsimp [reach] at rlr
      obtain ⟨n,hnl⟩ := rlr
      use n
      let pisf := po_ideal_system_from_allone_lem α s hq1 x y n
      exact (po_ideal_system_from_allone_lem α s hq1 x y n).mp hnl
}

--(hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1)のときに、Setup_spo2のidealのndsと、po_ideal_system_from_alloneで対応するpoのidealのndsと、が一致する。
--これは、直接対応するので示す必要はなさそう。
--示したいのは、poのidealのndsが常に非正であるときに、Setup_spo2のidealのndsも常に非正であることだが、上のことから自明。

lemma po_ideal_system_eq (s: Setup_spo α) (hq1:∀ q: Quotient s.setoid, (classOf s q).card = 1) :
  po_closuresystem (po_ideal_system_from_allone s hq1) = spo_closuresystem s:=
by
  dsimp [po_closuresystem, po_ideal_system_from_allone]
  dsimp [spo_closuresystem]
  simp
  ext ss
  constructor
  · intro h
    obtain ⟨hss, h⟩ := h
    --quotientをuseする必要あり。おそらくssを同値類に置き換えたもの。利用できる関数はあるか。
    use QuotientOf s (ss.subtype (fun x => x ∈ s.V))
    constructor
    · intro q hq q' hq'
      show q' ∈ QuotientOf s (Finset.subtype (fun x => x ∈ s.V) ss)
      let x:= q.out
      let x':= q'.out
      specialize h x x.property
      have : x.val ∈ ss :=
      by
        dsimp [QuotientOf] at hq
        rw [Finset.mem_image] at hq
        simp at hq
        obtain ⟨a,ha1,ha2⟩ := hq
        obtain ⟨ha2,ha3⟩ := ha2
        have : ⟨a,ha2⟩ = x :=
        by
          --equal_one
          let eo := equal_one s hq1 ⟨a,ha2⟩ x
          apply eo.mp
          subst ha3
          simp_all only [Subtype.coe_eta, Quotient.out_eq, x]
        simp_all only [Subtype.coe_eta, Quotient.out_eq, coe_mem, le_refl, x]
        obtain ⟨val, property⟩ := x
        obtain ⟨val_1, property_1⟩ := x'
        rwa [← this]
      specialize h this
      specialize h x' x'.property
      have : (po_ideal_system_from_allone s hq1).po.le x' x :=
      by
        --hq'からいえるのだけど、補題があったほうがいいかも。reachを一旦挟む？
        --po.leをfqに変換する方法は？
        rw [←(po_ideal_system_from_allone s hq1).order]
        dsimp [reach]
        rw [s.h_spo] at hq'
        dsimp [partialOrderOfFq] at hq'
        dsimp [reach] at hq'
        obtain ⟨n,hq'⟩ := hq'
        use n
        let pisfa := po_ideal_system_from_allone_lem α s hq1 x' x n
        have :s.fq^[n] ⟦x'⟧ = ⟦x⟧ :=
        by
          subst hq'
          simp_all only [Subtype.coe_eta, Quotient.out_eq, x, x']
        let pis := pisfa.mp this
        exact pis
      specialize h this
      dsimp [QuotientOf]
      rw [Finset.image]
      simp
      use x'
      constructor
      · simp_all only [x, x']
      · simp_all only [Subtype.coe_eta, Quotient.out_eq, coe_mem, exists_const, x, x']

    · constructor
      · simp_all only
      · intro hhs
        constructor
        · intro x hx
          dsimp [QuotientOf]
          rw [Finset.image]
          simp
          use x
          use hx
          have :x ∈ s.V :=
          by
            simp_all only
            exact hhs hx
          use this
        · intro q hq --もしかして、この部分の証明はhの条件を使わないのかも。ゴールがふつつの頂点ではない。
          --hqだけで証明できるかもしれない。
          intro x hx hh
          have xeqq: x = q.out :=
          by
            --上の定理のどれかでいえそう。
            symm
            let eo := equal_one2 s hq1 ⟨x,hx⟩
            subst hh
            simp_all only [eo]
          dsimp [QuotientOf] at hq
          rw [Finset.mem_image] at hq
          simp at hq
          obtain ⟨a,ha,ha2⟩ := hq
          obtain ⟨ha2,ha3⟩ := ha2
          have : x = a :=
          by
            have :@Quotient.mk _ s.setoid ⟨x,hx⟩ = @Quotient.mk _ s.setoid ⟨a,ha2⟩ :=
            by
              subst ha3 xeqq
              simp_all only [Subtype.coe_eta, Quotient.out_eq]
            let eo := equal_one s hq1 ⟨x,hx⟩ ⟨a,ha2⟩
            subst ha3 xeqq
            simp_all only [Subtype.coe_eta, Quotient.out_eq]
            cases eo
            simp_all only [Subtype.coe_eta, Quotient.out_eq, forall_const, imp_self]
          rw [this]
          exact ha
  · intro h
    obtain ⟨q, hq⟩ := h
    obtain ⟨hq1, hq2, hq3⟩ := hq
    constructor
    · simp_all only [forall_true_left]
    · intro x1 hx1 hx2 x2 hx21 hx22
      simp_all only [forall_true_left]
      obtain ⟨left, right⟩ := hq3
      apply right
      · apply hq1
        on_goal 2 => {exact hx22
        }
        · simp_all only
      · rfl
