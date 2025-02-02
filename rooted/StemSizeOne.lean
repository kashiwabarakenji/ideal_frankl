import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Finset.Union
import Mathlib.Tactic
import rooted.CommonDefinition
import rooted.RootedCircuits
import rooted.RootedImplication
import rooted.RootedFrankl
import rooted.RootedSets
import rooted.Preorder
import LeanCopilot

open Classical

--subtypeを使うように変更した。preoderの話は台集合の概念がないので、直接使いずらい。
def R_from_RS1 {α : Type} [DecidableEq α] (RS : RootedSets α) : {x // x ∈ RS.ground} → {x // x ∈ RS.ground} → Prop :=
  λ (x y:RS.ground) => ∃ r ∈ RS.rootedsets, r.root = y ∧ r.stem = {x.val}

--表現のステムの大きさがすべて1であれば、RSのから作った集合族とステム1から作ったpreorderのイデアルが一致する。
lemma size_one_preorder_lemma {α : Type} [DecidableEq α] [Fintype α]
  (RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
  (h₁ : ∀ p ∈ RS.rootedsets, p.stem.card = 1) :
  let SF := rootedsetToClosureSystem RS
  ∀ s : Finset RS.ground, SF.sets (s.image Subtype.val) ↔ (s ∈ (preorder.S (R_from_RS1 RS))) :=
by
  -- SFを定義展開しておく。
  intro SF s
  -- まず，RSから定義されるfilteredFamilyは
  --    s ∈ filteredFamily RS ↔ ∀ p ∈ RS.rootedsets, ¬(p.stem ⊆ s ∧ p.root ∉ s)
  -- である．また，SF.sets sは filteredFamily RS に s が属することと同値．
  --
  -- 一方，R_from_RS1 RS は，任意の x,y に対して，
  --    R_from_RS1 RS x y ↔ ∃ p ∈ RS.rootedsets, p.root = x ∧ p.stem = {y}
  -- と定められており，S (R_from_RS1 RS) は
  --    s ∈ S (R_from_RS1 RS) ↔ ∀ (x y : α), (∃ p ∈ RS.rootedsets, p.root = x ∧ p.stem = {y}) →
  --                             (x ∈ s → y ∈ s)
  -- である．
  --
  -- ここで，各 p ∈ RS.rootedsets について h₁ により p.stem は1元集合となるが，
  -- ValidPair の条件から p.root ∉ p.stem である．したがって，
  --  p.stem = {y} とすると p.root ≠ y であり，
  -- filteredFamilyの条件は「もし y ∈ s ならば p.root ∈ s」
  -- と書き換えられる．一方，S (R_from_RS1 RS) の条件は「もし p.root ∈ s ならば y ∈ s」
  -- であり，これらは互いの対偶条件（「y ∉ sならば p.root ∉ s」）で同値．
  --
  -- 以下，両側含意を示す．
  apply Iff.intro
  · -- SF.sets s → s ∈ S (R_from_RS1 RS)
    intro hs
    -- hs : ∀ p ∈ RS.rootedsets, ¬(p.stem ⊆ s ∧ p.root ∉ s)
    dsimp [preorder.S]
    simp only [Finset.mem_filter]
    constructor
    simp_all only [Finset.mem_univ, SF]
    intro x y hR
    -- hR : ∃ p ∈ RS.rootedsets, p.root = x ∧ p.stem = {y}
    obtain ⟨p, hp, py, hstem_eq⟩ := hR
    -- h₁より，p.stem.card = 1．
    have : p.stem = {x.val} := hstem_eq
    -- ここで，filteredFamilyの条件 hs p hp は
    --    ¬({y} ⊆ s ∧ p.root ∉ s) となる．
    -- しかし {y} ⊆ s ↔ y ∈ s なので，
    --    y ∈ s → p.root ∈ s
    -- となる．すなわち，対偶で p.root ∉ s → y ∉ s である．
    -- 今，x = p.root であり，仮定 hxs : x ∈ s なので，p.root ∈ s でなければならない．
    by_contra hxy
    push_neg at hxy  -- hxy : p.root ∈ s ∧ y ∉ s
    have hstem : {x} ⊆ s := by simp_all only [Finset.singleton_subset_iff, SF]--simp [hxy.2]
    have :p.stem ⊆ s.image Subtype.val :=
    by
        rw [this]
        simp_all only [Finset.singleton_subset_iff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
          Subtype.coe_eta, Finset.coe_mem, exists_const, SF]

    have : p.root ∈ s.image Subtype.val := by
      apply rootedpair_compatible RS (s.image Subtype.val) hs p hp
      simp_all only [Finset.singleton_subset_iff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
        Subtype.coe_eta, Finset.coe_mem, exists_const, SF]
    simp_all only [not_true_eq_false, and_false, SF] --hs p hp hstem,
    simp_all only [Finset.singleton_subset_iff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
      Subtype.coe_eta, Finset.coe_mem, exists_const]
    --contradiction
  · -- s ∈ S (R_from_RS1 RS) → SF.sets s
    intro hs
    -- すなわち，∀ (x y), (∃ p ∈ RS.rootedsets, p.root = x ∧ p.stem = {y}) →
    --           (x ∈ s → y ∈ s)
    -- となっている．
    -- SF.sets s の条件は ∀ p ∈ RS.rootedsets, ¬(p.stem ⊆ s ∧ p.root ∉ s) であるが，
    -- p ∈ RS.rootedsets について p.stem は1元集合なので，p.stem = {y} である．
    --intro p hp
    by_contra hnot
    push_neg at hnot  -- hnot : p.stem ⊆ s ∧ p.root ∉ s
    -- p.stem = {y} となる y をひとつとる．
    --have hcard := h₁ p hp  -- p.stem.card = 1
    dsimp [preorder.S] at hs
    simp [Finset.mem_filter] at hs
    dsimp [SF] at hnot
    dsimp [rootedsetToClosureSystem] at hnot
    dsimp [filteredFamily] at hnot
    simp at hnot
    have eq_ground:SF.ground = RS.ground := by
      simp_all only [SF]
      rfl
    have : s.image Subtype.val ⊆ SF.ground := by
      rw [eq_ground]
      simp_all only [SF]
      intro x hx
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      obtain ⟨w, h⟩ := hx
      simp_all only

    let hn := hnot this
    obtain ⟨p, hp,hstem,hterm⟩ := hn
    let hcard := h₁ p hp
    have :∃ y, y ∈ p.stem ∧ p.stem = {y} :=
    by
      let fc := (Finset.card_eq_one).mp hcard
      simp_all only [forall_const, SF]
      obtain ⟨w, h⟩ := fc
      simp_all only [Finset.singleton_subset_iff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
        Finset.mem_singleton, Finset.singleton_inj, exists_eq_left]

    obtain ⟨y, hy, hstem_eq⟩ := this
    -- hnot : {y} ⊆ s ∧ p.root ∉ s なので y ∈ s

    have hy_in_s : y ∈ s.image Subtype.val := by
      simp_all only [Finset.singleton_subset_iff, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
        Finset.mem_singleton, SF]
    -- 一方，R_from_RS1 RS の定義より，
    -- p ∈ RS.rootedsets と p.stem = {y} ならば
    -- (p.root ∈ s → y ∈ s) が成立する．
    -- すなわち，その対偶より，(y ∉ s → p.root ∈ s) である．
    -- しかし hnot.right より p.root ∉ s であるから y ∉ s となる．
    have contr : y ∉ s.image Subtype.val :=
    by
        -- hs より，∀ (x y), (∃ p, p ∈ RS.rootedsets ∧ p.root = x ∧ p.stem = {y})
        -- → (x ∈ s → y ∈ s)．
      contrapose! hs
      use y
      have : y ∈ RS.ground := by
        let rsi := (RS.inc_ground p hp).1
        simp_all only [Finset.singleton_subset_iff, forall_true_left, Finset.mem_singleton, Finset.mem_image,
          Subtype.exists, exists_and_right, exists_eq_right, forall_const, SF]
        obtain ⟨w, h⟩ := hnot
        obtain ⟨w_1, h_1⟩ := hs
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        simp_all only
      use this
      use p.root
      have :p.root ∈ RS.ground := by
        --rw [←eq_ground]
        exact (RS.inc_ground p hp).2
      use this
      constructor
      · dsimp [R_from_RS1]
        use p
      · constructor
        · simp_all only [Finset.singleton_subset_iff, forall_true_left, Finset.mem_singleton, Finset.mem_image,
          Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, SF]
        · simp_all only [Finset.singleton_subset_iff, forall_true_left, Finset.mem_singleton, Finset.mem_image,
          Subtype.exists, exists_and_right, exists_eq_right, not_false_eq_true, SF]
    simp_all only [Finset.singleton_subset_iff, Finset.mem_singleton, SF]

/-
証明の要点：

1. RS から定義される SF.sets s は「任意の p ∈ RS.rootedsets について，
   p.stem ⊆ s ならば p.root ∈ s」であるが，
   ただし各 p の stem は1元集合（h₁より）であるから，
   これは「もし y ∈ s ならば p.root ∈ s」（ただし p.stem = {y}）と同値である．
2. 一方，S (R_from_RS1 RS) の定義は「任意の x, y について，
   (∃ p ∈ RS.rootedsets, p.root = x ∧ p.stem = {y}) ならば
   (x ∈ s → y ∈ s)」である．
3. ValidPair の条件より p.root ∉ p.stem であるため，
   「もし y ∈ s ならば p.root ∈ s」と「もし p.root ∈ s ならば y ∈ s」
   は対偶をとると同値になる．

以上から両者は同値であることがわかる．
-/

lemma size_zero_rooted_sets [Fintype α](RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
  :
  let SF := rootedsetToClosureSystem RS
  (∃ p ∈ RS.rootedsets, p.stem.card = 0) ↔
  ¬ (SF.sets ∅) :=
  by
    simp
    dsimp [rootedsetToClosureSystem]
    dsimp [filteredFamily]
    simp

/-Aの提案で作ったが、使えなさそう。
lemma lemma_A (RS : RootedSets α) (q : ValidPair α)
  (hq : q ∈ RS.rootedsets)
  (x : { a // a ∈ RS.ground }) (hx : x.val ∈ q.stem) :
  Relation.ReflTransGen (R_from_RS1 RS) x ⟨q.root, (RS.inc_ground q hq).2⟩ :=
sorry

/- 補題B: 与えられた任意の関係 R と x, y に対して，
   Relation.ReflTransGen R x y から R_hat R x y が導かれる。
   （これはすでに与えられている補題 ReflTransGen.to_R_hat の形と同じです。）
-/
lemma lemma_B {R : α → α → Prop} {x y : α} [Fintype α]
  (h : Relation.ReflTransGen R x y) : preorder.R_hat R x y :=
sorry

/- 補題C: 任意の x と q.root に対して，
   R_hat (R_from_RS1 RS) x q.root が成立すれば，
   x を唯一の要素とする根付き集合 r （すなわち r.stem = {x} かつ r.root = q.root）
   が RS.rootedsets に存在する。
-/
lemma lemma_C (RS : RootedSets α) (q : ValidPair α)
  (hq : q ∈ RS.rootedsets)
  (x : { a // a ∈ RS.ground }) (h_Rhat : preorder.R_hat (R_from_RS1 RS) x ⟨q.root, (RS.inc_ground q hq).2⟩) :
  ∃ r ∈ RS.rootedsets, r.root = q.root ∧ r.stem = {x.val} :=
sorry

/- これら補題A，B，Cから，次の独立補題が導けます：
   任意の RS, q ∈ RS.rootedsets, そして任意の x ∈ q.stem に対して，
   x を唯一の要素とする根付き集合が存在する。
-/
--示したいことと、qの仮定が違っている。この言明は全く成り立たない。
lemma exists_singleton_rootedpair (RS : RootedSets α)
  (q : ValidPair α) (hq : q ∈ RS.rootedsets)
  (x : { a // a ∈ RS.ground }) (hx : x.val ∈ q.stem) :
  ∃ r ∈ RS.rootedsets, r.root = q.root ∧ r.stem = {x.val} :=
by
  -- 補題Aより，x から q.root への反射‐推移閉包が得られる
  have h_RT : Relation.ReflTransGen (R_from_RS1 RS) x ⟨q.root, (RS.inc_ground q hq).2⟩:=
    lemma_A RS q hq x hx
  -- 補題Bより，その反射‐推移閉包から R_hat (R_from_RS1 RS) x q.root が得られる
  have h_Rhat : preorder.R_hat (R_from_RS1 RS) x ⟨q.root, (RS.inc_ground q hq).2⟩ :=
    lemma_B h_RT
  -- 補題Cより，R_hat (R_from_RS1 RS) x q.root から目的の根付き集合が存在する
  exact lemma_C RS q hq x h_Rhat
-/

lemma size_one_rooted_circuits [Fintype α](RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
  (h₁ : ∀ p ∈ RS.rootedsets, p.stem.card = 1) :
  let SF := rootedsetToClosureSystem RS
  (p ∈ RS.rootedsets → p.stem.card = 1) →
  ∀ q, q ∈ (rootedcircuits_from_RS (rootedSetsFromSetFamily SF.toSetFamily)).rootedsets → q.stem.card = 1 :=
by
  intro SF h_singleton q hq
  -- rootedcircuits_from_RSはRS.rootedsetsをフィルタしているので，q ∈ (rootedcircuits_from_RS ...).rootedsets
  -- ならば q ∈ RS.rootedsets である．
  -- よって，仮定 h₁ より q.stem.card = 1 である．
  --intro h_one
  --RSからpreorderを作ることができる。
  let R: α → α → Prop := λ x y => ∃ r ∈ RS.rootedsets, r.root ∈ r.stem ∧ x = r.root ∧ y ∈ r.stem
  --Rのidealと誘導された集合族が等しくなる。
  --let R_hat: α → α → Prop := sorry

  by_cases h_card : q.stem.card = 1
  · exact h_card
  · have h_not1 : q.stem.card ≠ 1 := h_card
    have hasempty: SF.sets ∅ := by
      let sz := size_zero_rooted_sets RS
      simp at sz
      contrapose! sz
      right
      constructor
      · intro p hp
        let hcard := h₁ p hp
        simp_all only [implies_true, not_false_eq_true, ne_eq, SF]
        apply Aesop.BuiltinRules.not_intro
        intro a
        apply sz
        simp_all only
        simp [a] at hcard
      · simp_all only [implies_true, not_false_eq_true, ne_eq, SF]

    --rootedcircuits_makes_same_setfamilyでrootedcircuitsで集合族が変わらないことがわかる。
    --ClosureSystemTheoremで、もともとのemptyがrootedSetsFromSetFamily SF.toSetFamilyの集合族でも。
    have hasempty2: (rootedsetToClosureSystem (rootedSetsFromSetFamily SF.toSetFamily)).sets ∅ := by
      apply ClosureSystemTheorem SF ∅
      exact hasempty

    have hasempty3: ∀ r,r ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets → r.stem.card ≠ 0 := by
      intro r hr
      let szr := (size_zero_rooted_sets (rootedSetsFromSetFamily SF.toSetFamily)).mp
      simp at szr
      contrapose! szr
      simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, and_true, SF]
      use r

    have : q.stem.Nonempty := by
      apply Finset.card_ne_zero.mp
      intro h
      apply h_not1
      rw [h]
      simp
      dsimp [rootedcircuits_from_RS] at hq
      rw [Finset.mem_filter] at hq
      let he := hasempty3 q hq.1
      contradiction

    have : q.stem.card > 1 :=
    by
      cases qs:q.stem.card with
      | zero =>
        -- A.card = 0 の場合，nonemp から矛盾
        simp_all only [implies_true, zero_ne_one, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt,
          not_lt_zero', Finset.not_nonempty_empty, SF]
      | succ n =>
        match n with
        | 0 =>
          -- A.card = 1 の場合，h_not1 から矛盾
          contradiction
        | k+1 =>
          -- A.card = k+2 ≥ 2
          simp_all only [implies_true, add_left_eq_self, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
            not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one,
            or_true, SF]

    let A := (q.stem.attach).biUnion (λ xInStem =>
               Finset.univ.filter (λ z => Relation.ReflTransGen R xInStem.val z))
    --Finset.biUnion s t is the union of t a over a ∈ s.

    have h_stem_in_A : q.stem ⊆ A :=
    by
      dsimp [A]
      intro x hx
      simp
      use x

    have h_A_in_SF : SF.sets A :=
    by
      dsimp [SF]
      dsimp [rootedsetToClosureSystem]
      dsimp [filteredFamily]
      simp
      constructor
      · intro p hp
        dsimp [A] at hp
        rw [Finset.mem_biUnion] at hp
        obtain ⟨x, hx_in, hz_in⟩ := hp
        rw [Finset.mem_filter] at hz_in
        have : ∀ a1 a2 :α, a1 ∈ RS.ground → R a1 a2 → a2 ∈ RS.ground := by
          intro a1 a2 ha1
          dsimp [R]
          intro hr
          obtain ⟨r, hr_RS, hroot, hstem⟩ := hr
          let rsi := (RS.inc_ground r hr_RS).1
          simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, Finset.mem_attach,
            Finset.mem_univ, true_and, SF, A, R]
          obtain ⟨val, property⟩ := x
          obtain ⟨left, right⟩ := hstem
          subst left
          simp_all only
          apply rsi
          simp_all only
        sorry  --inductionだと思われるが、なにをinductionすればいいのか。

      · --rootedpair_compatibleはAがhyperedgeであるとわかってないと使えない。
        --ここは、Aの定義から示す必要がある。
        intro p hp
        dsimp [A]
        intro hs
        simp
        show ∃ a ∈ q.stem, Relation.ReflTransGen R a p.root
        --dsimp [A] at h_stem_in_A
        sorry --pのstemはAの中に入っているので、ReflTransGenの定義より、p.rootが入っているはず。
        --aとしてはp.rootに辿れるaがあるはずなので、それを使えばよいが、どうすればいいか。
        --h_stem_in_Aをもっと分解するといいのか?

    by_cases h_A : q.root ∈ A
    case pos =>
      -- A が q.root を含む場合
      -- すなわち，∃ x ∈ q.stem, R x q.root が成立する

    --q.stemから要素を取り出す。
    --obtain ⟨x, hx_in⟩ := Finset.exists_mem_of_ne_empty q.stem (Finset.nonempty_iff_ne_empty.mp this)

      have q_in_RS : q ∈ RS.rootedsets := by --間違っているかも。RSではなくて、推移性が成り立つR_hatのほうかも。
        dsimp [rootedcircuits_from_RS] at hq
        rw [Finset.mem_filter] at hq
        sorry

      --AIを参考に作ったが、この方針ではダメだと思われるので以下も意味がないかも。

      have hx_R : ∃ r ∈ RS.rootedsets, r.root = q.root ∧ r.stem = {x} :=
      by
        simp_all only [implies_true, not_true_eq_false, SF]
        --exact exists_singleton_rootedpair RS q q_in_RS ⟨x, q.stem.subset_of_mem hx_in⟩ hx_in

      obtain ⟨r, hr_RS, rroot_eq, h_stem⟩ := hx_R

      have h_proper : r.stem ⊂ q.stem :=
      by
        rw [h_stem]
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor

        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, Finset.singleton_subset_iff, SF]

        intro h_eq
        rw [←h_eq] at h_not1
        simp at h_not1
        simp_all only [implies_true, not_true_eq_false, SF]

      have :r ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets:=
      by
        let rir := rootedgenerator_is_rootedset RS r hr_RS
        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, SF]

      have h_min := (Finset.mem_filter.mp hq).2 r this rroot_eq

      specialize h_min h_proper
      simp_all only [implies_true, not_true_eq_false, ne_eq, Finset.card_eq_zero, SF]

    case neg =>
      -- A が q.root を含まない場合
      -- すなわち，∀ x ∈ q.stem, ¬ R x q.root が成立する
      --qのstemがAに含まれて、qのrootがAに含まれないが、Aは、RSと両立することが示せるので、
      --矛盾が生じる。
      sorry

  --ここまでを整理
  --qの極小性の条件は、hq_minに入っている。
  --示すべきことは、閉集合族SFから作られた極小な根付き集合は、ステムのサイズが1であること。
  --ひとつのあり得べき方針としては、極小な根付き集合が、ステムのサイズが2以上である場合に、矛盾を示すこと。
  --ステムサイズが1以上から推論できる根付き集合は、極小なステムサイズが1しかないので、
  --帰納法的な議論になると思われるが、なにに関する帰納法なのか思いついていない。
  --preorderの話だけでは、証明が完了しない。ステムの大きさが2のものは、preorderの話では登場しないが、
  --ここでは、rooted circuitsの話をしているので、極小なサイズ2のステムがないことを証明することになる。
  --サイズ2のステムがあるとそれは、hyperedgeにはならないことになる。
  --その根付きサーキットのせいで集合族が変わってくることになる。
  --しかし、集合族は、Rのtransitive closureで決まってくるのでこれはおかしい。
  --transitive closureに対応する根付き集合は、すべて根付きサーキットになっている。
  --これ以外にステムサイズ2以上の根付きサーキットがあると、集合族が変わってくることをまず示す。
  --足しても変わらない場合は、根付き集合が極小でない場合。極小なん極小な根付き集合、すなわち
  --根付きサーキットを足すと、集合族がかならず変わる。
  --rがそのような根付きサーキットだとすると、rが極小であるとすると、足す前のhyperedge sで、
  --r.root notin sかつr.stem ⊆ sとなるものがある。
  --ステムの真部分集合は、(r.stem - z) ∪ {r.root}となる。


def is_size_one_circuit (RS : RootedSets α):Prop:=
  ∀ p ∈ (rootedcircuits_from_RS RS).rootedsets, p.stem.card = 1
--rootedcircuits_from_RS RSの定義は、ステムの極小元を持ってきているだけなので、弱い。
--でもそんなこともない気もする。包含関係で大きいものは条件として使われないので、極小なものだけが意味がある。
--全部の根付き集合を考えている場合はそれでもよいが、部分的な表現だと、極小なものしか残さないと
--導かれる集合族が変わってきてしまうということはないという理解であっているか。
/- 一旦、お蔵入り。復活できるか考える。証明ができないというよりも命題がおかしいと思う。
2項関係とPreorderとイデアルの関係をよく考えて、どのような言明が一番よいのかを考える。

lemma size_one_circuits (RS : RootedSets α) (SF:ClosureSystem α) [DecidablePred SF.sets]
 (eq:  rootedsetToClosureSystem RS = SF) :
  is_size_one_circuit RS → q ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets →
  ∃ r ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets, q.root = r.root ∧ r.stem ⊆ q.stem ∧ r.stem.card = 1 :=
by
  intro h_one
  intro q_in_RS
  dsimp [is_size_one_circuit] at h_one
  dsimp [rootedcircuits_from_RS] at h_one
  --dsimp [rootedSetsFromSetFamily] at q_in_RS
  --dsimp [rootedSetsSF] at q_in_RS
  --これは違う。常に成り立つとは限らない。RSがすべての根付き集合を含んでいるとは限らないので。
  --have :q ∈ Finset.filter (fun q => ∀ r ∈ RS.rootedsets, r.root = q.root → ¬r.stem ⊂ q.stem) RS.rootedsets:=
  --h_oneの対偶のの命題を証明する。これは、この定理の言明とほぼ同じかも。
  simp at h_one
  --have : ∀ q ∈ RS.rootedsets, q.stem.card > 1 → ∃ r ∈ RS.rootedsets, r.root = q.root → r.stem ⊆ q.stem ∧ r.stem.card = 1:=
  --仮定から直接、証明することができない。集合を経由する必要がある。
      --別の言い方をすれば、極小ステムが、生成の根付き集合表現に入っているとは限らない。
      --別の言い方をすれば、ステムサイズ1の根付き集合表現からは、誘導されるものも含めて、任意の根付き集合に対して、サイズ1のものが極小ステムが1になる。
      --定理の言明自体は、今のところ正しいかもと思っている。このhaveは、RS.rootedsetsの中からとろうとしていて間違い。
  have : ∀ q ∈ RS.rootedsets, q.stem.card > 1 → ∃ r ∈ (rootedcircuits_from_RS (rootedSetsFromSetFamily SF.toSetFamily)).rootedsets, r.root = q.root ∧ r.stem ⊆ q.stem ∧ r.stem.card = 1:=
  by
      intro p p_in_RS
      intro h_card
      contrapose! h_one
      --今の段階でpは、内部にステム1を持たないような根付き集合になっている。
      use p
      constructor
      · exact p_in_RS

      · constructor
        · intro q' hq qp
          --成り立つかどうか、よく考える。
          have :q' ∈ (rootedcircuits_from_RS (rootedSetsFromSetFamily SF.toSetFamily)).rootedsets:=
          by
            dsimp [rootedcircuits_from_RS]
            dsimp [rootedSetsFromSetFamily]
            dsimp [rootedSetsSF]
            rw [Finset.mem_filter]
            rw [Finset.mem_image]
            simp
            constructor
            · dsimp [allCompatiblePairs]
              dsimp [isCompatible]
              simp
              use q'.stem --そもそもここで、q'を代入するのは正しいのかと思ったけど、このツリーは証明完了済み。
              use q'.root
              simp
              constructor
              · dsimp [allPairs]
                rw [Finset.product]
                apply Finset.mem_product.mpr
                let rsi := RS.inc_ground q' hq
                have : RS.ground = SF.ground:=
                by
                  subst eq
                  simp_all only [gt_iff_lt, ne_eq]
                  obtain ⟨left, right⟩ := rsi
                  simp_all only
                  rfl
                constructor
                · simp
                  rw [←this]
                  exact rsi.1

                · simp
                  rw [←this]
                  exact rsi.2

              · constructor
                · exact q'.root_not_in_stem

                · intro t hset qt
                              --tとRSの関係は、rootedsetToClosureSystem RS = SF
                  dsimp [rootedsetToClosureSystem] at eq
                  cases eq
                  simp at q_in_RS
                  simp at h_one
                  simp at hset
                  dsimp [filteredFamily] at hset
                  simp at hset
                  let hst := hset.2 q' hq qt
                  exact hst

            · --q'が極小であることを示すところ。そのための条件は揃っているのか？
              intro q'' hq' x hx h
              rw [←h]
              intro hh
              intro hhh
              simp_all
              subst hh
              rw [h] at hh
              --現状で仮定に矛盾があるかどうかは発見できていない。
              --q’とかq''のまわりに極小性がないので、矛盾している世に感じない。
              --h_oneは使うのか？
              --RS.rootedsetsの極小なものからq'をとった方が良いのでは。
              sorry
          sorry
        · subst eq
          simp_all only [gt_iff_lt, ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [lt_self_iff_false]
          --let ho := h_one q hq
  sorry
-/
