--このファイルは、functionalの議論の基本的な定義を行う。Setupなど。
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

set_option maxHeartbeats 2000000

open Finset Set Classical

variable {α : Type} [Fintype α] [DecidableEq α]

--Main定理を述べるのに必要だからここにおいている。
--Setupは、Preorderのところしか出てこないので、Setupに関する部分はPreorderのところに移動可能かと思ったら、
--preclosuresystemも同様。
--合わせて、Setupの定義に関連する補題をいくつか。
--eqClass_setupの定義に関係する部分。
--reachに関する部分。

------------
--setupの定義に必要な部分。
--fからRootedSetを作る関数。
--この形が一番良いか？alpha上のRootedSetsを与える。集合族を定義するのにこの形を利用している。
--functionalMainの主定理でもこの定義が参照されている。
--これをSetupから使えるようにしたのが、rootedset_from_setup。
noncomputable def rootedset_onestem_eachvertex_V {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:Finset.Nonempty V): RootedSets α :=
{
  ground := V,
  rootedsets :=
  V.attach.image (λ v => ValidPair.mk ({(f v).val}:Finset α) v (by
    have : v ∉ ({f v}:Finset V) := by
      simp_all only [ne_eq, Subtype.forall, Finset.mem_singleton]
      obtain ⟨val, property⟩ := v
      apply Aesop.BuiltinRules.not_intro
      intro a
      exact valid _ _ a.symm
    simp
    by_contra h_contra
    --cases h_contraこれを入れるとbyでエラー
    simp_all only [Finset.mem_singleton, ne_eq]
    have h_eq : v = f v := by
      apply Subtype.eq
      exact h_contra
    contradiction
  ))

  inc_ground := by
    intros p hp
    specialize hp
    constructor
    · simp at hp
      obtain ⟨v, ⟨hv, ⟨hv_in, hp_in⟩⟩⟩ := hp
      simp
    ·
      simp_all only [Finset.mem_image, mem_attach, true_and, Subtype.exists]
      obtain ⟨w, h⟩ := hp
      obtain ⟨w_1, h⟩ := h
      subst h
      simp_all only

  nonempty_ground := by
    simp_all only [ne_eq, Subtype.forall, attach_nonempty_iff]
  }

--setupを定義する時に利用している。fからpreorderを定義。
noncomputable def size_one_preorder {α : Type} [Fintype α] [DecidableEq α] (V: Finset α) (f : V → V) (valid:∀ v : V, f v ≠ v) (nonemp:V.Nonempty):
  Preorder { x // x ∈ V } := size_one_circuits_preorder (rootedset_onestem_eachvertex_V V f valid nonemp)


--前順序が同値類を作り、それ上の半順序を作るという一般的な話の部分。setoidが導入されている。Setupに利用される。
def equiv_rel {α : Type} [Preorder α] (x y : α) : Prop := x ≤ y ∧ y ≤ x

lemma equiv_rel_refl {α : Type} [Preorder α]  : Reflexive (@equiv_rel α _) := fun x => ⟨le_refl x, le_refl x⟩

lemma equiv_rel_symm  {α : Type} [Preorder α] : Symmetric (@equiv_rel α _) :=
  fun (x y : α) (h : equiv_rel x y) => ⟨h.2, h.1⟩

lemma equiv_rel_trans {α : Type} [Preorder α] : Transitive (@equiv_rel α _) :=
  fun _ _ _ ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨le_trans h1 h3, le_trans h4 h2⟩

lemma equiv_rel_equiv {α : Type}  [Preorder α]: Equivalence (@equiv_rel α _) :=
  ⟨equiv_rel_refl, @equiv_rel_symm α _, @equiv_rel_trans α _⟩

--preorderから定義するsetoidの定義。setupの定義で用いる。
def setoid_preorder {α : Type}[Preorder α]: Setoid α := ⟨@equiv_rel α _, equiv_rel_equiv⟩

--normalized degree sumが非正になる程度の強さはある。
structure Setup (α : Type) [Fintype α] [DecidableEq α] where
  (V        : Finset α)
  (nonemp   : V.Nonempty)
  (f        : V → V)
  (valid    : ∀ v : V, f v ≠ v)
  (pre      : Preorder {x // x ∈ V})
  (h_pre    : pre = size_one_preorder V f valid nonemp)
  (setoid   : Setoid {x // x ∈ V})
  (h_setoid : setoid = setoid_preorder) --これは順序ではなく、同値類まで。

--size_one_preorderは、ステムから定義されている。
--rootedset_onestem_eachvertex_Vからrootedsetが定義されて、
--そのステムの大きさが1なので、size_one_circuits_preorderで前順序が定義されている。
--本当はfから直接前順序を定義した方が証明は簡単だったか。これはtransitive closureによる定義。
--その関係は、size_one_preorder_eq_transitionで示されている。

instance (s : Setup α) : Preorder {x // x ∈ s.V} := s.pre

----------------------
--setupの定義からClosure Systemを導入する部分。
-----------------------

--setupからrootedsetを作るもの。fから作るには、rootedset_onestem_eachvertex_Vを利用すれば良い。setupに含めてもよいかも。
--RootedSetsから2項関係にするには、R_from_RS1 を用いると、ステムサイズ1のものだけから2項関係を作ってくれる。
noncomputable def rootedset_from_setup {α : Type} [Fintype α] [DecidableEq α] (s: Setup α) : RootedSets α :=
 rootedset_onestem_eachvertex_V s.V s.f s.valid s.nonemp

lemma rootedset_from_setup_ground (s:Setup α) :
  (rootedset_from_setup s).ground = s.V :=
by
  rfl

--このときのRootedSetsのステムのサイズがすべて1であること。
lemma rootedsetset_from_setup_has_stem1 (s: Setup α) :
 ∀ p ∈ (rootedset_from_setup s).rootedsets, p.stem.card = 1 :=
by
  dsimp [rootedset_from_setup]
  dsimp [rootedset_onestem_eachvertex_V]
  intro p hp
  rw [Finset.mem_image] at hp
  obtain  ⟨a, ha⟩ := hp
  rw [←ha.2]
  simp

--setupを与えたときのClosureSystemを与える関数。
--次のpre_closuresystem2のように定義する方法もある。
--定義は、functionalTreeIdealの中に移動した方が良いかと思ったが、メイン定理を述べるのに必要だから
--ここにおいているよう。
noncomputable def pre_closuresystem (s:Setup α): ClosureSystem α :=
{
  ground := s.V
  sets := fun ss : Finset α => ss ⊆ s.V ∧(∀ v : s.V, v.val ∈ ss → (∀ w : s.V, s.pre.le w v → w.val ∈ ss)),
  inc_ground:= by
    intro ss a
    exact a.1
  nonempty_ground := by
    exact s.nonemp
  has_ground := by
    simp_all only
    constructor
    · simp_all only [subset_refl]
    ·
      intro v a a_1
      intro a_2
      simp_all only [coe_mem]
  intersection_closed := by
    intro s t a b
    simp_all only
    constructor
    ·
      obtain ⟨left, right⟩ := a
      obtain ⟨left_1, right_1⟩ := b
      intro v hv
      simp_all only [Finset.mem_inter]
      obtain ⟨left_2, right_2⟩ := hv
      simp_all only [Subtype.forall]
      apply left_1
      simp_all only
    ·
      intro v a_1 w a_2
      simp_all only [Subtype.forall, Finset.mem_inter]
      obtain ⟨val, property⟩ := v
      obtain ⟨val_1, property_1⟩ := w
      obtain ⟨left, right⟩ := a
      obtain ⟨left_1, right_1⟩ := b
      obtain ⟨left_2, right_2⟩ := a_1
      simp_all only
      apply And.intro
      · tauto
      · tauto
}

--集合族をrootedcircircuits経由で別に定義。同値性は、ideal_system_eq_lemで示される。
--functionalMainの中で使う。
noncomputable def pre_closuresystem2 (s:Setup α): ClosureSystem α :=
 rootedsetToClosureSystem (rootedset_from_setup s)
--既存の関数を利用した形で定義されているが、rootedsetToClosureSystemが複雑なので簡単になってないかも。

--preorderidealsytemは、rootedsetToClosureSystem(rootedset_onestem_eachvertex_V)と等しくなるのか。
--既存の定理を利用する形で証明できないか。rootedToClosureSystemとidealの関係の定理を探す。
--表現のステムの大きさがすべて1であれば、RSのから作った集合族とステム1から作ったpreorderのイデアルが一致する。
--lemma size_one_preorder_lemma {α : Type} [DecidableEq α] [Fintype α]
--  (RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
--  (h₁ : ∀ p ∈ RS.rootedsets, p.stem.card = 1) :
--  let SF := rootedsetToClosureSystem RS
--  ∀ s : Finset RS.ground, SF.sets (s.image Subtype.val) ↔ (s ∈ (preorder.S_R (R_from_RS1 RS))) :=

--後ろで使っている。
lemma subtype_subset_attach {α : Type} (ss t : Finset α)  :
    Finset.subtype (fun x => x ∈ t) ss ⊆ t.attach :=
by
  intro x hx
  simp_all only [mem_subtype, mem_attach]

-- 大小関係と寝付きサーキットから定義するpreorderの関係。
-- 両向き。size_one_preorder_setup_lemmaと同じか。
lemma le_eq_R (s : Setup α) (x y : {x // x ∈ s.V}) :
  s.pre.le y x ↔ preorder.R_hat (R_from_RS1 (rootedset_from_setup s)) x y :=
by
  apply Iff.intro
  · intro hxy
    rw [s.h_pre] at hxy
    dsimp [size_one_preorder] at hxy
    dsimp [size_one_circuits_preorder] at hxy
    dsimp [rootedset_from_setup]
    exact hxy
  · intro hxy
    rw [s.h_pre]
    dsimp [size_one_preorder]
    dsimp [size_one_circuits_preorder]
    dsimp [rootedset_from_setup] at hxy
    exact hxy

--ふたつの定義が同値であることを示す。本質的には、size_one_preorder_setで示したこと。
--それに気がつくのが遅かったので、証明はもっと短くなるかも。
--functionalMainの主定理の証明でも使われている。
lemma pre_closuresystem_eq_lem (s : Setup α) :
   pre_closuresystem s = pre_closuresystem2 s :=
by
  let sopl := size_one_preorder_lemma (rootedset_from_setup s)
  have :∀ p ∈ (rootedset_from_setup s).rootedsets, #p.stem = 1 :=
  by
    exact fun p a => rootedsetset_from_setup_has_stem1 s p a
  specialize sopl this
  simp at sopl
  dsimp [pre_closuresystem]
  dsimp [pre_closuresystem2  ]
  ext ss
  ·
    rfl
  · constructor
    · intro h
      have : ss ⊆ (rootedset_from_setup s).ground :=
      by
        exact h.1
      let ss_attach : Finset { x // x ∈ (rootedset_from_setup s).ground } :=
        ss.subtype (fun x => x ∈ (rootedset_from_setup s).ground)
      specialize sopl ss_attach
      have :(Finset.image Subtype.val ss_attach) = ss:=
      by
        ext y
        constructor
        · intro hh
          rw [Finset.mem_image] at hh
          simp at hh
          dsimp [ss_attach]
          dsimp [ss_attach] at hh
          obtain ⟨hh1,hh⟩ := hh
          rw [Finset.mem_subtype] at hh
          simp at hh
          exact hh
        · intro hh
          rw [Finset.mem_image]
          dsimp [ss_attach]
          simp
          constructor
          · exact hh
          · exact this hh

      rw [this] at sopl
      apply sopl.mpr
      dsimp [ss_attach]
      dsimp [preorder.S_R]
      dsimp [preorder.closedUnder]

      simp at h
      rw [s.h_pre] at h
      dsimp [size_one_preorder] at h
      dsimp [size_one_circuits_preorder] at h
      dsimp [rootedset_from_setup]
      dsimp [preorder.R_hat] at h
      dsimp [preorder.S_R] at h
      dsimp [preorder.closedUnder] at h
      simp at h
      simp
      obtain ⟨h1,h2⟩ := h

      constructor
      · -- (rootedset_onestem_eachvertex_V s.V s.f ⋯ ⋯).groundはs.Vではないか。
        suffices Finset.subtype (fun x => x ∈ s.V) ss ⊆ s.V.attach from by
          exact this
        let ssa := subtype_subset_attach ss s.V
        convert ssa

      · intro w1 hw1 w2 hw2 hh whh1
        specialize h2 w1 hw1 whh1
        specialize h2 w2 hw2
        apply h2
        intro s2 hs2 hhs2 hhhs2
        exact hhs2 w1 hw1 w2 hw2 hh hhhs2

    · intro h
      have hsub : ss ⊆ (rootedset_from_setup s).ground :=
      by
        dsimp [rootedset_from_setup]
        dsimp [rootedset_onestem_eachvertex_V]
        have :(rootedsetToClosureSystem (rootedset_from_setup s)).ground = s.V :=
        by
          rfl
        exact (rootedsetToClosureSystem (rootedset_from_setup s)).inc_ground ss h

      -- `ss` を subtype 化
      let ss_attach : Finset {x // x ∈ (rootedset_from_setup s).ground} :=
        ss.subtype (fun x => x ∈ (rootedset_from_setup s).ground)

      -- `Finset.image Subtype.val ss_attach = ss`
      have himg : Finset.image Subtype.val ss_attach = ss := by
        ext x
        constructor
        · intro hx
          rw [Finset.mem_image] at hx
          --使うのは、hxとss_attachの定義と、
          simp at hx
          obtain ⟨w,hx⟩ := hx
          dsimp [ss_attach] at hx
          simp_all only [mem_subtype, ss_attach]
          --rcases hx with ⟨⟨y,hy⟩,hy_in,rfl⟩
          --exact hy_in
        · intro hx
          simp_all only [attach_image_val, ss_attach]
          rw [Finset.mem_image]
          simp
          constructor
          · exact hx
          · exact hsub hx
      ------------------------------------------------------------------
      -- `pre_closuresystem2` の closedUnder 部分から
      --   ss_attach ∈ preorder.S_R …
      ------------------------------------------------------------------
      have hS : ss_attach ∈ preorder.S_R (R_from_RS1 (rootedset_from_setup s)) := by
        dsimp [ss_attach]
        show Finset.subtype (fun x => x ∈ (rootedset_from_setup s).ground) ss ∈ preorder.S_R (R_from_RS1 (rootedset_from_setup s))
        --spolで変換したあとにhを使うと思われる。
        have hsets :
          (rootedsetToClosureSystem (rootedset_from_setup s)).sets
            (Finset.image Subtype.val ss_attach) := by
          -- `h : … .sets ss` を `himg` で書き換えるだけ
           simpa [himg] using h
        exact (sopl ss_attach).mp hsets


      constructor
      · exact hsub
      · intro w1 hw1 w2 hw2
        dsimp [preorder.S_R] at hS
        rw [Finset.mem_filter] at hS
        dsimp [preorder.closedUnder] at hS
        have eq_ground:(rootedset_from_setup s).ground = s.V :=
        by
          exact rfl
        obtain ⟨hS1,hS2⟩ := hS

        have hS2':  ∀ ⦃x y : { x // x ∈ s.V}⦄,
           R_from_RS1 (rootedset_from_setup s) x y → x ∈ ss_attach → y ∈ ss_attach :=
        by
          intro x y
          intro a a_1
          simp_all only [Finset.mem_powerset, mem_subtype, Subtype.forall, ss_attach]
          simp_all only [ss_attach]
          obtain ⟨val_2, property_2⟩ := x
          obtain ⟨val_3, property_3⟩ := y
          tauto

        -- 1.  w2 ≤ w1  を  R_from_RS1 w1 w2  に変換。後ろで使っている。
        have hR :  preorder.R_hat (R_from_RS1 (rootedset_from_setup s)) w1 w2 :=
        by
          exact (le_eq_R s w1 w2).mp hw2

        -- 2.  w1 ∈ ss_attach
        have hw1_in : (w1 : {x // x ∈ s.V}) ∈ ss_attach := by
          -- `Finset.mem_subtype` 展開
          have : (w1 : α) ∈ ss := hw1
          have hground : (w1 : α) ∈ s.V := w1.property
          -- ss_attach = ss.subtype hsub なので両方満たせば OK
          simp_all only [Finset.mem_powerset, mem_subtype, Subtype.forall, coe_mem, ss_attach]

        -- 3.  hS2' を使って w2 ∈ ss_attach
        dsimp [rootedset_from_setup] at hS2'
        --simp at hS2'
        have ideal_eq_ss :preorder_ideal (rootedset_from_setup s) ss_attach = Finset.subtype (fun x => x ∈ s.V) ss :=
        by
          have hsubs : ss_attach =
              Finset.subtype (fun x : α => x ∈ s.V) ss :=
          by
            -- 定義と `eq_ground` を展開すれば同型
            exact rfl

          rw [←hsubs]
          show (preorder_ideal (rootedset_from_setup s)) ss_attach = ss_attach

          rw [←himg] at h
          let sops := size_one_preorder_set (rootedset_from_setup s) (rootedsetset_from_setup_has_stem1 s) ss_attach h
          exact sops

        let RS := rootedset_from_setup s
        have : (w2 : α) ∈ ss := by
          -- 1. w1 ∈ preorder_ideal …
          have hw1_ideal : w1 ∈ preorder_ideal RS ss_attach := by
            -- 単に witness を w1 自身にすればよい
            have hw1_attach : w1 ∈ ss_attach := hw1_in
            have : (w1 : α) ∈ RS.ground := w1.property

            simp_all only [Finset.mem_powerset, mem_subtype, Subtype.forall, coe_mem, ss_attach, RS]

          -- 2. イデアル閉包で w2 も入る。simp_allで利用している。
          have hw2_ideal :=
            preorder_ideal_closed_lemma (RS := RS) (s := ss_attach)
              w1 w2 hR hw1_ideal

          -- 3. イデアル=ss で書き換え
          simp_all only [Finset.mem_powerset, mem_subtype, Subtype.forall, RS, ss_attach]

        exact this

-------------
--Setupに関する同値類の関係。SetupにはSetoidが導入されているのにsetoidを使ってないのは、それ以前に作ったものだからかも。

--下で使っている。Setupの枠組みで、同値な要素全体を与える。
noncomputable def eqClass_setup (s: Setup α) (x : {x : α // x ∈ s.V}) : Finset {x // x ∈ s.V} :=
  s.V.attach.filter (fun y => s.setoid.r x y)

--同じ同値類に入っている要素には大小関係がある。
lemma eqClass_le (s: Setup α) : (x y: {x : α // x ∈ s.V}) → y ∈ eqClass_setup s x → s.pre.le x y :=
by
  intro x y h
  simp [eqClass_setup] at h
  rw [s.h_setoid] at h
  simp_all only [AntisymmRel.setoid_r]
  obtain ⟨val, property⟩ := x
  obtain ⟨val_1, property_1⟩ := y
  exact h.1

--上の逆向き。
lemma eqClass_ge (s: Setup α) : (x y: {x : α // x ∈ s.V}) → y ∈ eqClass_setup s x → s.pre.le y x :=
by
  intro x y h
  simp [eqClass_setup] at h
  rw [s.h_setoid] at h
  simp_all only [AntisymmRel.setoid_r]
  obtain ⟨val, property⟩ := x
  obtain ⟨val_1, property_1⟩ := y
  exact h.2

--逆に、前順序で同値ならば、eqClassでも同値。
lemma eqClass_eq (s: Setup α) : (x y: {x : α // x ∈ s.V}) → s.pre.le x y →s.pre.le y x → eqClass_setup s x = eqClass_setup s y :=
by
  intro x y hxy hyx
  ext z
  apply Iff.intro
  ·
    simp [eqClass_setup]
    rw [s.h_setoid]
    simp_all only [AntisymmRel.setoid_r]
    dsimp [AntisymmRel]
    intro h
    constructor
    · exact LE.le.trans_antisymmRel hyx h

    · exact AntisymmRel.trans_le (id (And.symm h)) hxy
  ·
    simp [eqClass_setup]
    rw [s.h_setoid]
    simp_all only [AntisymmRel.setoid_r]
    obtain ⟨xval, xproperty⟩ := x
    obtain ⟨yval, yproperty⟩ := y
    dsimp [AntisymmRel]
    intro h
    constructor
    ·
      exact s.pre.le_trans ⟨xval, xproperty⟩ ⟨yval, yproperty⟩ z hxy h.1
    ·
      exact s.pre.le_trans z ⟨yval, yproperty⟩ ⟨xval, xproperty⟩ h.2 hyx

--必要に迫られて作った。同値な要素は、前順序でも同値。
lemma eqClass_eq_rev (s: Setup α) : (x y z: {x : α // x ∈ s.V}) → x ∈ eqClass_setup s z → y ∈ eqClass_setup s z → s.pre.le x y ∧ s.pre.le y x:=
by
  intro x y z hx hy
  constructor
  · dsimp [eqClass_setup] at hx
    dsimp [eqClass_setup] at hy
    rw [s.h_setoid] at hx hy
    simp_all only [AntisymmRel.setoid_r]
    --obtain ⟨xval, xproperty⟩ := x
    --obtain ⟨yval, yproperty⟩ := y
    simp_all only [mem_filter, mem_attach, true_and]
    --obtain ⟨val, property⟩ := z
    rw [AntisymmRel] at hx hy
    obtain ⟨left, right⟩ := hx
    obtain ⟨left_1, right_1⟩ := hy
    exact right.trans left_1
  · dsimp [eqClass_setup] at hx
    dsimp [eqClass_setup] at hy
    rw [s.h_setoid] at hx hy
    simp_all only [AntisymmRel.setoid_r]
    --obtain ⟨xval, xproperty⟩ := x
    --obtain ⟨yval, yproperty⟩ := y
    simp_all only [mem_filter, mem_attach, true_and]
    --obtain ⟨val, property⟩ := z
    rw [AntisymmRel] at hx hy
    obtain ⟨left, right⟩ := hx
    obtain ⟨left_1, right_1⟩ := hy
    apply Preorder.le_trans
    assumption
    simp_all only

---
--Setupに直接関係ない部分。より抽象化されている。

def reach {A : Type} (f : A → A) (x y : A) : Prop :=
  ∃ n : ℕ, f^[n] x = y

lemma reach_trans {A : Type} (f : A → A) {x y z : A}
  (hxy : reach f x y) (hyz : reach f y z) :
  reach f x z := by
  obtain ⟨n, hn⟩ := hxy
  obtain ⟨m, hm⟩ := hyz
  exists (n + m)
  subst hn hm
  rw [←Function.iterate_add_apply]
  rw [add_comm]
