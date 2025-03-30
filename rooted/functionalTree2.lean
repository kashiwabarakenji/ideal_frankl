import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
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
import rooted.functionalCommon
import rooted.functionalPreorder
import rooted.functionalTree


open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]
--ここまでで、サイズが2以上の同値類は、極大なものしかないことを証明した。
--この次は、任意のノードの上には、極大なノードの同値類がちょうど1つ存在することを示すことになる。
--1つ以上存在することの証明と、2つあったら一致することの証明を分けた方がいいか。
--一つあることは、たどれるノードは有限個でそこからもっとも遠いところをとってくれば、極大要素に
--なることを示せばよいか。ただ、道の存在定理が示す道の長さは最短路とは限らなかった。
--大小関係を持つ2つの頂点を与えると最短路を与える関数を作る必要がある。
--補題。もっとも遠い距離の点は、極大要素になる。
--証明。もっとも遠い距離の点から1歩進んだところは同値な頂点になるので、サイズが2以上になり、極大要素になる。
--辿り着ける極大な同値類が2つもってくると、必ず一致することを示す必要がある。
--2つの頂点に辿り着くまでのパスが同じことを示すのがよいか。これも帰納法か。
--補題。あるノードから2つの頂点にたどり着いたときに、その頂点の近い方までの道は一致する。
--補題。あるノードから歩数が決まれば、道が確定し、頂点が決定する。
--その道上以外にそのノードよりも上のものは存在しないし、上のものはかならず道上にある。



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
  have h_eq_class : eqClass V x.val = Finset.image (λ v => v) {v | f v = x.val} ∪ ({x}:Finset V) := by
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

--def fiterate (s: Setup α) (x : α) (n : ℕ) : α :=
--  s.f^[n] x

--iterationで辿り着くものには、大小関係がある。
lemma iteratef_lemma (s: Setup α) (x : s.V):
  ∀ n, s.pre.le x (s.f^[n] x) := by
  intro n
  induction n generalizing x
  case zero =>
      simp_all only [Function.iterate_zero, id_eq, le_refl]

  case succ n ih =>
      rw [Function.iterate_succ]
      simp
      have ihh:s.pre.le (s.f x) (s.f^[n] (s.f x)) := by
        simp_all only [Subtype.forall]
      have : s.pre.le (x) (s.f x) := by
        apply f_and_pre
        simp_all only [Subtype.forall]
      exact s.pre.le_trans x (s.f x) (s.f^[n] (s.f x)) this ihh

--大小関係があるとiterationで辿り着く。
lemma iteratef_lemma_ref (s: Setup α) (x y: s.V) (h: s.pre.le x y):
  ∃ n:Nat, (s.f^[n] x)=y := by
  let pes := path_exists_setup s x y h
  obtain ⟨n, h⟩ := pes
  use n
  obtain ⟨z, hz0,hzn, hz⟩ := h
  have nnf: ∀ nn : Fin (n+1), z nn = s.f^[nn.val] x := by
      let motive : Fin (n+1) → Prop := fun nn => z nn = s.f^[nn.val] x
      apply (@Fin.induction (n) motive)
      case zero =>
        subst hzn hz0
        simp_all only [Fin.natCast_eq_last, Fin.val_zero, Function.iterate_zero, id_eq, motive]
      case succ =>
        intro i hi
        dsimp [motive] at hi
        dsimp [motive]
        rw [←(hz i)]
        rw [hi]
        rw [← hz0]
        --rw [@subtype_val_eq]
        exact Eq.symm (Function.iterate_succ_apply' s.f (↑i) (z 0))
  have h_lt : n < n + 1 := by exact lt_add_one n
  let nnff :=nnf (Fin.mk n h_lt)
  simp at nnff
  rw [←nnff]
  rw [←hzn]
  simp
  congr

lemma iteratef_lemma_two (s: Setup α) (x: s.V) (n1 n2: Nat) :
  n1 < n2 → s.pre.le (s.f^[n1] x) (s.f^[n2] x) :=
by
  -- ここで f の n 回の反復を考えます
  intro h
  let n := n2 - n1
  have : n + n1 = n2 := by
    simp_all only [n]
    obtain ⟨val, property⟩ := x
    omega
  have : s.f^[n] (s.f^[n1] x) = s.f^[n2] x := by
    rw [←this]
    rw [Function.iterate_add]
    exact rfl
  let il := iteratef_lemma s (s.f^[n1] x) n
  rw [this] at il
  exact il

--補題:fのiterationの全体は、重複しているものがある。
--証明：鳩の巣原理。
lemma iteratef_pegion (s: Setup α) (x: s.V)  : ∃ (n1 n2: Nat), n1 ≠ n2 ∧ (s.f^[n1] x) = s.f^[n2] x :=
by
  let dom := (Finset.Icc 0 (s.V.card + 1)).image (fun i => (s.f^[i] x))
  have : s.V.card < ((Finset.Icc 0 (s.V.card + 1))).card := by
    simp_all only [Nat.card_Icc, tsub_zero, ge_iff_le]
    obtain ⟨val, property⟩ := x
    linarith
  have : Fintype.card { x // x ∈ s.V } < Fintype.card (Finset.Icc 0 (s.V.card + 1)) :=
  by
    simp_all only [Nat.card_Icc, tsub_zero, Fintype.card_coe, Finset.mem_Icc, zero_le, true_and]
  have : Fintype.card { x // x ∈ s.V } < Fintype.card (Fin (#s.V + 1)) := by
    simp_all only [Nat.card_Icc, tsub_zero, Fintype.card_coe, Finset.mem_Icc, zero_le, true_and, Fintype.card_fin,
      lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt]

  let fe := @Fintype.exists_ne_map_eq_of_card_lt (Fin (s.V.card + 1)) s.V _ _ (λ i=> s.f^[i.val] x) this
  obtain ⟨n1, n2, h⟩ := fe
  use n1, n2
  simp_all only [Nat.card_Icc, tsub_zero, Fintype.card_coe, Finset.mem_Icc, zero_le, true_and, Fintype.card_fin,
    lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, ne_eq, and_true]
  obtain ⟨val, property⟩ := x
  obtain ⟨left, right⟩ := h
  apply Aesop.BuiltinRules.not_intro
  intro a
  simp_all only
  omega

--otera
lemma iteratef_pegion_ordered (s : Setup α) (x : s.V) :
  ∃ (n1 n2 : ℕ), n1 < n2 ∧ (s.f^[n1] x) = (s.f^[n2] x) := by
  obtain ⟨n1, n2, hne, heq⟩ := iteratef_pegion s x
  by_cases h : n1 < n2
  · exact ⟨n1, n2, h, heq⟩
  · have h' : n2 < n1 := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) hne.symm
    simp_all only [ne_eq, not_lt]
    obtain ⟨val, property⟩ := x
    apply Exists.intro
    · apply Exists.intro
      · apply And.intro
        · exact h'
        · simp_all only

  --補題：何回もiterationすると、サイズが2以上の同値類に辿り着く。
  --証明：鳩の巣の上の補題のn1とn2のノードは同じで、その次のノードは、異なるが同じ同値類に属するノードになる。
lemma iteratef_size2 (s: Setup α) (x: s.V)  : ∃ (n : Nat), 2 ≤ (eqClass_setup s (s.f^[n] x)).card :=
by
  let h := iteratef_pegion_ordered s x
  /- hの別の分解の仕方。参考まで。
  cases h with
  | intro n1 h' =>
    cases h' with
    | intro n2 h'' =>
      cases h'' with
      | intro hneq heq =>
      -- ここで n1, n2, hneq, heq が使える
  -/
  --obtain ⟨n1, n2, hneq, heq⟩ : ∃ n1 n2, n1 ≠ n2 ∧ s.f^[n1] x = s.f^[n2] x := h
  obtain ⟨n1, n2, hneq, heq⟩ := h
  let y := s.f^[n1] x
  let z := s.f^[n1+1] x
  have y12: y = s.f^[n2] x := by
    simp_all only [y]
  have fzy: z = s.f y := by
    dsimp [y]
    exact Function.iterate_succ_apply' s.f n1 x
  have neqyz: y ≠ z := by
    intro h
    rw [fzy] at h
    let hnot :=  s.valid y
    rw [Eq.symm h] at hnot
    contradiction
  have : s.pre.le y z := by
    exact f_and_pre s y z (id (Eq.symm fzy))
  have : n2 > n1 + 1:= by
    by_cases n2 = n1 + 1
    case pos h =>
      rw [h] at y12
      rw [h] at hneq
      have : y = s.f (s.f^[n1] x) :=
      by
        exact False.elim (neqyz y12)
      have :y = s.f y := by
        exact this
      have :y ≠ s.f y := by
        exact fun a => neqyz y12
      contradiction
    case neg h =>
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, y, z]
      omega

  have : s.pre.le z y := by
    --zからyにfで行けるので、s.pre.le z yとなる。
    let ilt := iteratef_lemma_two s x (n1+1) n2 this
    dsimp [y,z]
    simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, ge_iff_le, y, z]
    rwa [← fzy]
  have yineq: y ∈ eqClass_setup s y := by
    simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, y, z]
    rw [eqClass_setup]
    simp_all only [mem_filter, mem_attach, true_and]
    rfl

  have : z ∈ eqClass_setup s y := by
    dsimp [eqClass_setup]
    simp_all only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, mem_attach, y, z]
    ·
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, y, z]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      obtain ⟨val_2, property_2⟩ := z
      symm
      rw [← fzy]
      simp_all only
      symm
      rw [← fzy]
      simp_all only
      induction s
      rename_i h_pre h_setoid po this_2
      subst h_pre h_setoid
      simp_all only [AntisymmRel.setoid_r]
      constructor
      · simp_all only
      · simp_all only
  have : (eqClass_setup s y).card ≥ 2 := by
    dsimp [eqClass_setup]
    simp_all only [Finset.card_filter, Finset.card_univ, true_and, Finset.mem_univ, Finset.mem_filter]
    --zも(eqClass_setup s y).cardの要素で、neqyzなので、同値類の大きさは2以上。
    have hsub : {y, z} ⊆ eqClass_setup s y := by
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, y, z]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      obtain ⟨val_2, property_2⟩ := z
      intro x hx
      simp_all only [Finset.mem_insert, Finset.mem_singleton]
      obtain ⟨val_3, property_3⟩ := x
      cases hx with
      | inl h => simp_all only
      | inr h_1 => simp_all only
    have hsub_card: ({y,z}:Finset s.V).card ≤ (eqClass_setup s y).card := by
      exact Finset.card_le_card hsub
    have :({y,z}:Finset s.V).card = 2:= by
      simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, Finset.mem_singleton,
        not_false_eq_true, card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd, y, z]
    rw [this] at hsub_card
    simp
    simp_all only [Function.iterate_succ, Function.comp_apply, ne_eq, gt_iff_lt, Finset.mem_singleton,
      not_false_eq_true, card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd, y, z]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    obtain ⟨val_2, property_2⟩ := z
    exact hsub_card

  use n1

  --ここからは半順序に関するもの。

  --preorderの大きさ2以上の同値類は、半順序の極大要素になる。
  --preorderの極大要素は、同値類の極大要素になる。これは示し済み。
  --半順序で大小関係があったら、それをpullbachした前順序でも大小関係がある。示し済み。
  --前順序で大小関係があったら、それをpushforwardした半順序でも大小関係がある。示し済み。

--前順序の要素を対応する同値類に移す。setoid preorderのキメ打ちなので、setup系ではない。
--setupに対して、pullbackを定義した方が良い。
--noncomputable def pullback {α : Type} [Fintype α] [Preorder α]
--  (J : Finset (Quotient (@setoid_preorder α _))) : Finset α :=
--  { a : α | Quotient.mk setoid_preorder a ∈ J }
--noncomputable def pushforward {α : Type} [Fintype α] [Preorder α]
--  (I : Finset α) : Finset (Quotient (@setoid_preorder α _)) :=
--  Finset.univ.filter (fun q => ∃ a ∈ I, Quotient.mk setoid_preorder a = q)
--lemma quotient_le_iff {α : Type}[Preorder α] (a b : α) :
--  (quotient_partial_order.le (Quotient.mk setoid_preorder a : Quotient (@setoid_preorder α _))  (Quotient.mk setoid_preorder b)) ↔ a ≤ b := by

noncomputable def spullback  (s: Setup α) (J : Finset (Quotient s.setoid)) : Finset s.V :=
  { a : s.V | Quotient.mk s.setoid a ∈ J }

noncomputable def spushforward  (s: Setup α) (I : Finset s.V) : Finset (Quotient s.setoid) :=
  Finset.univ.filter (fun q => ∃ a ∈ I, Quotient.mk s.setoid a = q)

--instを入れなくても、自動的にs.poのインスタンスを使ってくれている。
lemma pullback_preorder_lemma (s : Setup2 α)-- [inst : PartialOrder (Quotient s.setoid)]
 (j1 j2 : (Quotient s.setoid)) (x1 x2 : s.V) :
  Quotient.mk s.setoid x1 = j1 → Quotient.mk s.setoid x2 = j2 → s.po.le j1 j2 → s.pre.le x1 x2 :=
by
  intro h1 h2 h3
  rw [@Setup2.h_po] at h3
  dsimp [partialOrder_from_preorder] at h3
  simp [LE.le, partialOrder_from_preorder, Quotient.lift₂] at h3
  subst h2 h1
  simp_all only [Quotient.lift_mk]

lemma pushforward_preorder_lemma (s : Setup2 α) (x1 x2 : s.V) :
  s.pre.le x1 x2 → s.po.le (Quotient.mk s.setoid x1)  (Quotient.mk s.setoid x2) :=
by
  intro h
  rw [@Setup2.h_po]
  dsimp [partialOrder_from_preorder]
  simp_all only

/--
商集合上 `(Quotient setoid_preorder, ≤)` における「極大元」であることを表す述語です。
-/
--この順序はPartial orderの順序。まだ使ってないかも。setupで書き直す。
def isMaximalQ (s : Setup2 α) (x : Quotient (s.setoid)) : Prop :=
  ∀ y, s.po.le x y → s.po.le y x

--lemma eqClass_size_ge_two_implies_inverse
--    {α : Type} [Fintype α] [DecidableEq α]
--    (s : Setup α)
--    (x : {x // x ∈ s.V})
--    (h : 2 ≤ (eqClass_setup s x).card) :
--  ∀ y : {x // x ∈ s.V},  s.pre.le x y → s.pre.le y x := by
-- で大きさ2以上の同値類は、極大になることをいっているが、極大性自体は定義していない。

--isMaximalの定義もsetupに合わせる必要があるのでは。
lemma isMaximal_iff (s: Setup2 α) (a : s.V) :
  isMaximal s a ↔ isMaximalQ s (Quotient.mk s.setoid a) := by
  constructor
  · --------------------
    -- (→) 方向の証明
    intro ha  -- `ha` : a は元の前順序で極大
    intro x hx
    -- x は商集合上の元なので、代表元 b を取り出す
    rcases Quotient.exists_rep x with ⟨b, rfl⟩
    -- hx : Quotient.mk a ≤ Quotient.mk b から a ≤ b を得る
    dsimp [isMaximal] at ha
    specialize ha b
    have : a ≤ b := by
      exact pullback_preorder_lemma s (Quotient.mk s.setoid a) (Quotient.mk s.setoid b) a b rfl rfl hx
    have : b ≤ a := by
      exact ha this
    apply pushforward_preorder_lemma s
    simp_all only [imp_self]
  · --------------------
    -- (←) 方向の証明
    intro ha  -- `ha` : 商集合で Quotient.mk a が極大
    intro b hab
    -- a ≤ b から商集合でも Quotient.mk a ≤ Quotient.mk b となる
    dsimp [isMaximalQ] at ha
    have : s.po.le (Quotient.mk s.setoid a) (Quotient.mk s.setoid b) := by
      exact pushforward_preorder_lemma s a b hab
    have : s.po.le (Quotient.mk s.setoid b) (Quotient.mk s.setoid a) := by
      simp_all only [imp_self]
    apply pullback_preorder_lemma s ⟦b⟧ ⟦a⟧ b a rfl rfl
    simp_all only

/--
「元の前順序での極大元の集合」-
「商集合上での極大元の集合」とが、商写像 `Quotient.mk` を通じて
ちょうど同じものになる、ということを集合レベルでも示せます。
-/
noncomputable def MaxSet (s:Setup2 α) := ({ a : s.V | isMaximal s a }:Finset s.V)
noncomputable def MaxQuotSet (s:Setup2 α) : Finset (Quotient (s.setoid)) :=
  { x : Quotient s.setoid | isMaximalQ s x }

lemma MaxQuotSet_eq_image (s:Setup2 α) :
  MaxQuotSet s = Finset.image (Quotient.mk (s.setoid)) (MaxSet s) := by
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
      simp_all only [mem_attach, and_self]
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
      simp_all only [mem_attach, true_and]
      obtain ⟨val, property⟩ := b
      obtain ⟨val_1, property_1⟩ := a
      rw [isMaximal_iff] at ha
      apply ha
      simp_all only

--残った示すべきことは、半順序のほうで、
--各ノードに対して、唯一の極大元が存在するということがわかればよい。
--極大元の存在は比較的簡単。
--二つあったら一致することも証明できる。
--あと、setupを使って、ideal集合族が一致することを示す必要があるかも。
