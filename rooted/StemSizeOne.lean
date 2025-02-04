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
  ∀ s : Finset RS.ground, SF.sets (s.image Subtype.val) ↔ (s ∈ (preorder.S_R (R_from_RS1 RS))) :=
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
    dsimp [preorder.S_R]
    simp only [Finset.mem_filter]
    constructor
    · simp_all only [Finset.mem_univ, SF]
      let rcci := (rootedsetToClosureSystem RS).inc_ground (s.image Subtype.val)
      simp_all only [Finset.mem_powerset]
      intro x hx
      simp_all only [Finset.mem_attach]
    · intro x y hR
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
    dsimp [preorder.S_R] at hs
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
      dsimp [preorder.closedUnder]
      intro sr
      push_neg

      have :y ∈ RS.ground := by
        let rsi := (RS.inc_ground p hp).1
        simp_all only [Finset.singleton_subset_iff, forall_true_left, Finset.mem_singleton, Finset.mem_image,
          Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, SF]
        obtain ⟨w, h⟩ := hnot
        obtain ⟨w_1, h_1⟩ := hs
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        simp_all only
      use ⟨y, this⟩
      have : p.root ∈ RS.ground :=
      by
        exact (RS.inc_ground p hp).2
      use ⟨p.root,this⟩

      constructor
      · dsimp [R_from_RS1]
        use p
      · simp_all only [Finset.singleton_subset_iff, forall_true_left, Finset.mem_singleton, Finset.mem_image,
        Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, not_false_eq_true, and_self, SF]

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


noncomputable def preorder_ideal {α : Type} [DecidableEq α] [Fintype α]
  (RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
  (s : Finset RS.ground) : Finset RS.ground :=
  Finset.filter (λ x => ∃ y ∈ s, preorder.R_hat (R_from_RS1 RS) y x) RS.ground.attach

lemma preorder_extensive {α : Type} [DecidableEq α] [Fintype α]
  (RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
  (s : Finset RS.ground) : s ⊆ (preorder_ideal RS s) :=
by
  dsimp [preorder_ideal]
  intro x hx
  rw [Finset.mem_filter]
  constructor
  · simp_all only [Finset.mem_attach]
  · rw [preorder.R_hat_eq_ReflTransGen]
    simp
    use x
    simp_all only [Subtype.coe_eta, true_and, Finset.coe_mem, exists_const]
    obtain ⟨val, property⟩ := x
    rfl

--preorderのイデアルの集合preorder_idealは、本当にイデアルになっている。
lemma preorder_ideal_closed_lemma  {α : Type} [DecidableEq α] [Fintype α]
  (RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
  --(h₁ : ∀ p ∈ RS.rootedsets, p.stem.card = 1)
   (s : Finset RS.ground) :
  --let SF := rootedsetToClosureSystem RS
  ∀ x y : RS.ground, preorder.R_hat (R_from_RS1 RS) x y → x ∈ (preorder_ideal RS s)
  → y ∈ (preorder_ideal RS s) :=
by
  intro x y hxy hx
  dsimp [preorder_ideal] at hx
  simp at hx
  dsimp [preorder_ideal]
  simp
  rw [preorder.R_hat_eq_ReflTransGen]
  rw [preorder.R_hat_eq_ReflTransGen] at hxy hx
  obtain ⟨r, hr⟩ := hxy
  case refl =>
    obtain ⟨xx, hx, hR⟩ := hx
    use xx
    use hx

  case tail t1 t2 t3 =>
    obtain ⟨xx, hx, hR⟩ := hx
    use xx
    use hx
    let rr := Relation.ReflTransGen.tail t2 t3
    let rr2 := Relation.ReflTransGen.trans hR.2 rr
    constructor
    · simp_all only
    · simp_all only [rr2]

lemma find_source_of_ideal_element {α : Type} [DecidableEq α] [Fintype α]
  (RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
  (s : Finset RS.ground) (x : RS.ground) (hx : x ∈ (preorder_ideal RS s)) :
  ∃ y ∈ s, preorder.R_hat (R_from_RS1 RS) y x :=
by
  dsimp [preorder_ideal] at hx
  simp at hx
  obtain ⟨y, hy, hR⟩ := hx
  rw [preorder.R_hat_eq_ReflTransGen]
  simp
  obtain ⟨r, hr⟩ := hR
  rw [preorder.R_hat_eq_ReflTransGen] at hr
  constructor
  · exact ⟨_, r, hr⟩

--上のlemma　preorder_ideal_closed_lemmaを使って、証明をやり直したつもりだったが、結果的に使ってない。
--find_source_of_ideal_elementを使うように書き換えられるが、まだ行なっていない。
--この補題preorder_ideal_closedは、preorder_idealがhyperedgeであることを示す。
lemma preorder_ideal_closed {α : Type} [DecidableEq α] [Fintype α]
  (RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
  (h₁ : ∀ p ∈ RS.rootedsets, p.stem.card = 1) (s : Finset RS.ground) :
  let SF := rootedsetToClosureSystem RS
  SF.sets ((preorder_ideal RS s).image Subtype.val) :=
by
  simp
  dsimp [rootedsetToClosureSystem]
  dsimp [preorder_ideal]
  dsimp [filteredFamily]
  rw [preorder.R_hat_eq_ReflTransGen] --R_hatを分解せずにTransGenに持ち込むことが証明のポイント
  simp
  constructor
  · intro x hx --xは、preorder_idealの中から取る。
    simp_all only [Finset.mem_filter, Finset.mem_attach, Finset.mem_univ, Finset.mem_image, Subtype.exists,
      exists_and_right, exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]
    obtain ⟨hx, _, hR⟩ := hx --xの満たす性質が分解される。主な性質はhR
    simp_all only
  · --ここで示すべきことは、ステムを含んでいる場合に、ルートも含まれること。
    intro p hp --pがなにかというのが問題
    intro hpp --hppの条件がステムがidealに含まれるという条件を表している。これをうまく扱うのが証明のポイント

    have prg:p.root ∈ RS.ground :=
    by
      exact (RS.inc_ground p hp).2
    use prg  --不要なexistsを消すため。

    --コメントアウトするとエラーになるので、暗黙に使っている？
    have : ∀ x, x ∈ p.stem → x ∈ (preorder_ideal RS s).image Subtype.val :=
    by
      intro x hx
      simp_all only [Finset.mem_filter, Finset.mem_attach, Finset.mem_univ, Finset.mem_image, Subtype.exists,
        exists_and_right, exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const]
      dsimp [preorder_ideal]
      let hppx := hpp hx
      simp at hppx
      have :x ∈ RS.ground :=
      by
        obtain ⟨w, h⟩ := hppx
        simp_all only
      use this
      rw [Finset.mem_filter]
      constructor
      simp_all only [exists_true_left, Finset.mem_attach]

      rw [preorder.R_hat_eq_ReflTransGen]
      simp_all only [exists_true_left, Subtype.exists]

    --実は使ってないのか。参考までに消さずに残してもよい。
    /- have stem_in_ideal: p.stem ⊆ (preorder_ideal RS s).image Subtype.val :=
    by
      intro x hx
      exact this x hx
    -/

    --p.rootのひとつ上の要素がyとなる。
    have : p.stem.card = 1 := by
      exact h₁ p hp
    have :∃ y, y ∈ p.stem ∧ p.stem = {y} :=
    by
      let fc := Finset.card_eq_one.mp this
      obtain ⟨w, h⟩ := fc
      simp_all only [Finset.singleton_subset_iff, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and,
        Subtype.exists, exists_and_right, exists_eq_right, Finset.card_singleton, Finset.mem_singleton,
        Finset.singleton_inj, exists_eq_left]
    obtain ⟨y, hy, hstem_eq⟩ := this
    have yg:y ∈ RS.ground :=
    by
      let ri := (RS.inc_ground p hp).1
      simp_all only [Finset.singleton_subset_iff, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and,
        Subtype.exists, exists_and_right, exists_eq_right, Finset.card_singleton, Finset.mem_singleton]
      simp_all only [forall_eq]
      obtain ⟨w, h⟩ := hpp
      simp_all only

    have yp: (R_from_RS1 RS) ⟨y,yg⟩ ⟨p.root,prg⟩ :=
    by
      dsimp [R_from_RS1]
      use p

    --yの親玉がzとなる。
    have exists_z: ∃ z:s, preorder.R_hat (R_from_RS1 RS) z ⟨y,yg⟩ :=
    by
      rw [preorder.R_hat_eq_ReflTransGen]
      simp_all only [Finset.singleton_subset_iff, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and,
        Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, Finset.mem_singleton, forall_eq,
        exists_const, Finset.card_singleton, exists_prop]
    obtain ⟨z, hz⟩ := exists_z

    /- 実はつかってないのかも。同じことを下で証明しているので、使った形でも書き直せる可能性あり。しばらく残す。
    have pr_in_ideal : p.root ∈ (preorder_ideal RS s).image Subtype.val :=
    by
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_true_left]
      dsimp [preorder_ideal]
      rw [preorder.R_hat_eq_ReflTransGen]
      simp
      use z
      constructor
      · constructor
        · exact z.2
        · rw [preorder.R_hat_eq_ReflTransGen] at hz
          exact Relation.ReflTransGen.tail hz yp
    -/

    use z.val
    have : z.val.val ∈ RS.ground :=
    by
      simp_all only [Finset.singleton_subset_iff, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and,
        Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, Finset.mem_singleton, forall_eq,
        exists_const, Finset.card_singleton, Finset.coe_mem]

    use this
    constructor
    · simp_all only [Finset.singleton_subset_iff, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and,
      Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, Finset.mem_singleton, forall_eq,
      exists_const, Finset.card_singleton, Subtype.coe_eta, Finset.coe_mem]
    · rw [preorder.R_hat_eq_ReflTransGen] at hz
      simp_all only [Finset.singleton_subset_iff, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and,
        Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, Finset.mem_singleton, forall_eq,
        exists_const, Finset.card_singleton, Subtype.coe_eta]
      simp_all only [Finset.coe_mem]
      obtain ⟨val, property⟩ := z
      obtain ⟨w, h⟩ := hpp
      obtain ⟨val, property⟩ := val
      obtain ⟨w_1, h⟩ := h
      obtain ⟨left, right⟩ := h
      simp_all only
      constructor
      on_goal 2 => {exact yp
      }
      · simp_all only

--preorderのところにあるdown_closure_eq_Infの集合続版。preorderのほうの定理を利用しても証明できると思われるが、直接証明する。
lemma preorder_ideal_lemma {α : Type} [DecidableEq α] [Fintype α]
  (RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
  (h₁ : ∀ p ∈ RS.rootedsets, p.stem.card = 1) :
  let SF := rootedsetToClosureSystem RS
  ∀ s : Finset RS.ground,
  (preorder_ideal RS s).image Subtype.val = finsetIntersection (RS.ground.powerset.filter (fun (t : Finset α) => SF.sets t ∧ (s.image Subtype.val) ⊆ t)) :=
by
  intro SF s --sはhyperedgeとは限らない。
  ext ss --左の集合族からとってきた集合。
  simp
  constructor
  · intro hx
    simp at hx
    obtain ⟨hss, hR⟩ := hx
    dsimp [preorder_ideal] at hR
    have : (RS.ground.powerset.filter (fun (t : Finset α) => SF.sets t ∧ (s.image Subtype.val) ⊆ t)).Nonempty :=
    by
      use RS.ground
      simp
      constructor
      · exact SF.has_ground
      · show Finset.image Subtype.val s ⊆ RS.ground
        simp_all only [Subtype.exists, Finset.mem_filter, Finset.mem_attach, true_and]
        rw [Finset.image_subset_iff]
        intro x_1 a
        simp_all only [Finset.coe_mem]

    let mf :=@mem_finsetIntersection_iff_of_nonempty _ _ (RS.ground.powerset.filter (fun (t : Finset α) => SF.sets t ∧ (s.image Subtype.val) ⊆ t)) ss this
    apply mf.mpr --preorderの方の証明のFinset.mem_infに相当。
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨hSF, hst⟩ := hf.2
    rw [Finset.mem_filter] at hR
    obtain ⟨hR1, hR2⟩ := hR
    obtain ⟨y2, hy2, hR_hat⟩ := hR2
    --証明に使いそうな条件は、hR_hatとhstとhy2とhSF
    --have: x ∈ s.image Subtype.val := by --sはhyperedgeでないので、これは成り立たないのかも。
    have : y2.val ∈ f := by
      apply hst
      simp_all only [Finset.mem_powerset, and_true, Finset.mem_attach, Finset.mem_image, Subtype.exists,
        exists_and_right, exists_eq_right, Subtype.coe_eta, Finset.coe_mem, exists_const, SF]
    dsimp [preorder.R_hat] at hR_hat
    let hrh := hR_hat (f.subtype (fun x => x ∈ RS.ground))
    simp at hrh
    apply hrh
    · show Finset.subtype (fun x => x ∈ RS.ground) f ∈ preorder.S_R (R_from_RS1 RS)
      --このゴールはxとは関係ないゴール?そもそも成り立つのか？
      simp_all only [Finset.mem_powerset, and_true, Finset.mem_attach, forall_const, SF]
      obtain ⟨val, property⟩ := y2
      obtain ⟨left, right⟩ := hf
      simp_all only
      dsimp [preorder.S_R]
      rw [Finset.mem_filter]
      simp
      constructor
      · intro z hz
        simp_all only [Finset.mem_subtype, Finset.mem_attach]
      · show preorder.closedUnder (R_from_RS1 RS) (Finset.subtype (fun x => x ∈ RS.ground) f)
        intro x y rs xs
        let sop := (size_one_preorder_lemma RS h₁ (Finset.subtype (fun x => x ∈ RS.ground) f)).mpr
        simp at sop
        have :Finset.subtype (fun x => x ∈ RS.ground) f ∈ preorder.S_R (R_from_RS1 RS) :=
        by
          dsimp [preorder.S_R]
          simp
          dsimp [preorder.closedUnder]
          constructor
          · intro sss hsss
            simp_all only [Finset.mem_subtype, Finset.mem_attach]
          · intro xx yy rxy hxx
            dsimp [rootedsetToClosureSystem] at right
            dsimp [filteredFamily] at right
            simp at right
            obtain ⟨w, h⟩ := right
            dsimp [R_from_RS1] at rxy
            obtain ⟨r, hr, hroot, hstem⟩ := rxy
            have : r.stem ⊆ f:=
            by
              simp_all only [Finset.mem_subtype, Finset.singleton_subset_iff]
            --let hrh := h r hr this
            simp_all only [Finset.mem_subtype]
            obtain ⟨val_4, property_4⟩ := yy
            subst hroot
            simp_all only [Finset.singleton_subset_iff]
        /-
        have :ss ∈ f :=
        by
          apply hrh
          exact this
        -/
        have :(rootedsetToClosureSystem RS).sets (Finset.image Subtype.val (Finset.subtype (fun x => x ∈ RS.ground) f)):=
        by
          apply sop
          exact this

        dsimp [rootedsetToClosureSystem] at this
        dsimp [filteredFamily] at this
        simp at this
        obtain ⟨w, h⟩ := this

        dsimp [R_from_RS1] at rs
        obtain ⟨r, hr, hroot, hstem⟩ := rs
        have rf: r.stem ⊆ f:=
        by
          simp_all only [Finset.mem_subtype, Finset.singleton_subset_iff]
        simp_all only [forall_const, Finset.mem_subtype, Finset.singleton_subset_iff]
        obtain ⟨val_1, property_1⟩ := x
        obtain ⟨val_2, property_2⟩ := y
        subst hroot
        simp_all only [Finset.singleton_subset_iff, Finset.mem_image, Finset.mem_subtype, Subtype.exists,
          exists_and_left, exists_prop, exists_eq_right_right, and_self]

    simp_all only [Finset.mem_powerset, and_true, Finset.mem_attach, forall_const, SF]

  · intro hsss
    have h_assum: (RS.ground.powerset.filter (fun (t : Finset α) => SF.sets t ∧ (s.image Subtype.val) ⊆ t)).Nonempty :=
    by
      use RS.ground
      simp
      constructor
      · exact SF.has_ground
      · show Finset.image Subtype.val s ⊆ RS.ground
        rw [Finset.image_subset_iff]
        intro x_1 a
        simp_all only [Finset.coe_mem]
    let mf :=@mem_finsetIntersection_iff_of_nonempty _ _ (RS.ground.powerset.filter (fun (t : Finset α) => SF.sets t ∧ (s.image Subtype.val) ⊆ t)) ss h_assum
    rw [mf] at hsss
    simp at hsss
    have ssg: ss ∈ RS.ground :=
    by
      let hssg := hsss RS.ground
      simp at hssg
      let hssg := hssg SF.has_ground
      have : Finset.image Subtype.val s ⊆ RS.ground :=
      by
        simp_all only [SF]
        rw [Finset.image_subset_iff]
        intro x a
        simp_all only [Finset.coe_mem]
      exact hssg this
    constructor
    · --show ∃ a, ∃ (b : a ∈ RS.ground), ⟨a, b⟩ ∈ s ∧ preorder.R_hat (R_from_RS1 RS) ⟨a, b⟩ ⟨ss, _⟩
      --この集合がhyperedgeになることを示す。すると、この集合に入らない要素は、hyperedgeの共通部分に含まれない。
      --have :⟨ss, ssg⟩ ∈ preorder_ideal RS s := これはしょうめいしようとしていることではないのか。
      --obtain ⟨z,hz⟩ := find_source_of_ideal_element RS s ⟨ss,ssg⟩ これを使うためには、証明することを使うので直接は無理。
      --use z.val
      have pig: Finset.image Subtype.val (preorder_ideal RS s) ⊆ RS.ground :=
      by
        simp_all only [subset_refl, SF]
        simp [Finset.image_subset_iff]
      have s_in_ideal:Finset.image Subtype.val s ⊆ Finset.image Subtype.val (preorder_ideal RS s) :=
      by
        have :s ⊆ (preorder_ideal RS s) :=
        by
          exact preorder_extensive RS s
        simp_all only [subset_refl, SF]
        rw [Finset.image_subset_iff]
        intro x a
        simp_all only [subset_refl, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
          Subtype.coe_eta, Finset.coe_mem, exists_const]
        obtain ⟨val, property⟩ := x
        exact this a
      have : SF.sets ((preorder_ideal RS s).image Subtype.val):=
      by
        exact preorder_ideal_closed RS h₁ s
      let hssss := hsss ((preorder_ideal RS s).image Subtype.val) pig this s_in_ideal
      rw [Finset.mem_image] at hssss
      obtain ⟨a, ha, rfl⟩ := hssss
      exact ha

    /- 後ろのゴールがなくなった？
    · simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl, SF]
      rw [finsetIntersection] at mf
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_sup, id_eq, implies_true, and_true,
        iff_true, subset_refl, SF]
      obtain ⟨w, h⟩ := mf
      obtain ⟨left, right⟩ := h
      obtain ⟨left, right_1⟩ := left
      apply left
      simp_all only
    -/

lemma size_one_preorder_closure {α : Type} [DecidableEq α] [Fintype α]
  (RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
  (h₁ : ∀ p ∈ RS.rootedsets, p.stem.card = 1) :
  let SF := rootedsetToClosureSystem RS
  ∀ s : Finset RS.ground, closureOperator SF s = preorder_ideal RS s :=
by
  intro SF s
  dsimp [preorder_ideal] --closureOperatorは展開しない方がいい？
  simp
  sorry


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

  have q_in_RSS : q ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets := by
    dsimp [rootedcircuits_from_RS] at hq
    rw [Finset.mem_filter] at hq
    exact hq.1
  -- rootedcircuits_from_RSはRS.rootedsetsをフィルタしているので，q ∈ (rootedcircuits_from_RS ...).rootedsets
  -- ならば q ∈ RS.rootedsets である．
  -- よって，仮定 h₁ より q.stem.card = 1 である．
  --intro h_one
  --RSからpreorderを作ることができる。
  let R: α → α → Prop := λ x y => ∃ r ∈ RS.rootedsets, y = r.root ∧ r.stem = {x}
  --Rのidealと誘導された集合族が等しくなる。
  --let R_hat: α → α → Prop := sorry

  by_cases h_card : q.stem.card = 1
  case pos =>
    exact h_card
  case neg =>
    have h_not1 : q.stem.card ≠ 1 := h_card
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

    have q_ge_1: q.stem.card > 1 :=
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
    have ground_trans: ∀ a1 a2 :α, a1 ∈ RS.ground → R a1 a2 → a2 ∈ RS.ground := by
      intro a1 a2 ha1
      dsimp [R]
      intro hr
      obtain ⟨r, hr_RS, hroot, hstem⟩ := hr
      let rsi := (RS.inc_ground r hr_RS).2
      simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, Finset.mem_attach,
        Finset.mem_univ, true_and, SF, R]

    let A := (q.stem.attach).biUnion (λ xInStem =>
               Finset.univ.filter (λ z => Relation.ReflTransGen R xInStem.val z))
    --Finset.biUnion s t is the union of t a over a ∈ s.

    have A_in_ground: A ⊆ RS.ground := by
      intro a ha
      dsimp [A] at ha
      rw [Finset.mem_biUnion] at ha
      obtain ⟨x, hx_in, hz_in⟩ := ha
      rw [Finset.mem_filter] at hz_in
      cases hz_in.2 with
      | refl =>
        have qs := (rootedcircuits_from_RS (rootedSetsFromSetFamily SF.toSetFamily)).inc_ground q hq
        have : (rootedcircuits_from_RS (rootedSetsFromSetFamily SF.toSetFamily)).ground = RS.ground := by
          simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
            and_imp, Finset.mem_attach, Finset.mem_univ, true_and, SF, R]
          obtain ⟨val, property⟩ := x
          obtain ⟨left, right⟩ := qs
          simp_all only [SF]
          rfl
        rw [←this]
        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
          and_imp, Finset.mem_attach, Finset.mem_univ, true_and, SF, R]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := qs
        simp_all only [SF]
        tauto

      | tail h1 h2 =>
        let qs := (rootedcircuits_from_RS (rootedSetsFromSetFamily SF.toSetFamily)).inc_ground q hq
        have : (rootedcircuits_from_RS (rootedSetsFromSetFamily SF.toSetFamily)).ground = RS.ground := by
          simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
            and_imp, Finset.mem_attach, Finset.mem_univ, true_and, SF, R]
          obtain ⟨val, property⟩ := x
          obtain ⟨left, right⟩ := qs
          simp_all only [SF]
          rfl
        rw [←this]
        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
          and_imp, Finset.mem_attach, Finset.mem_univ, true_and, SF, R]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := qs
        simp_all only [SF]
        obtain ⟨r, hr_RS, hroot, hstem⟩ := h2
        have r_in_ground: r.root ∈ RS.ground := by
          let rsi := (RS.inc_ground r hr_RS).2
          simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, Finset.mem_attach,
            Finset.mem_univ, true_and, SF, R]

        have: r.stem.Nonempty := by
          apply Finset.card_ne_zero.mp
          intro h
          subst hroot
          simp_all only [Finset.card_singleton, one_ne_zero]

        obtain ⟨z, hz⟩ := this

        have z_in_ground: z ∈ RS.ground := by
          let rsi1 := (RS.inc_ground r hr_RS).1
          subst hroot
          simp_all only [Finset.mem_singleton]
          subst hz
          apply rsi1
          simp_all only [Finset.mem_singleton]

        have sz: r.stem = {z} :=
        by
          subst hroot
          simp_all only [Finset.mem_singleton]

        have :R z r.root := by
          dsimp [R]
          use r

        let gt := ground_trans z r.root z_in_ground r hr_RS
        simp at gt
        let gs := gt sz
        subst hroot
        exact gs

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
      · intro y hy
        dsimp [A] at hy
        rw [Finset.mem_biUnion] at hy
        obtain ⟨x, hx_in, hz_in⟩ := hy
        rw [Finset.mem_filter] at hz_in

        cases hz_in.2 with
        | refl =>
          have : x.val ∈ A:=
          by
            simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt,
              forall_exists_index, and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const,
              Subtype.forall, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_filter, Subtype.exists,
              exists_prop, SF, R, A]
            obtain ⟨val, property⟩ := x
            simp_all only
            exact ⟨val, property, hz_in⟩
          have : x.val ∈ RS.ground := by
            exact A_in_ground this
          simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
            and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const, Subtype.forall,
            Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_filter, Subtype.exists, exists_prop, SF, R, A]

          --exact hz_in.1
        | tail h1 h2 =>
          /-have : x.val ∈ A:= --これは使わないかもしれない。
          by
            simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt,
              forall_exists_index, and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const,
              Subtype.forall, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_filter, Subtype.exists,
              exists_prop, SF, R, A]
            obtain ⟨val, property⟩ := x
            simp_all only
            obtain ⟨w, h⟩ := h2
            obtain ⟨left, right⟩ := h
            obtain ⟨left_1, right⟩ := right
            subst left_1
            use val

          have : x.val ∈ RS.ground := by
            exact A_in_ground this
          -/
          --simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
          --  and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const, Subtype.forall,
          --  Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_filter, Subtype.exists, exists_prop, SF, R, A]
          show y ∈ RS.ground
          obtain ⟨r, hr_RS, hroot, hstem⟩ := h2
          let rsi := (RS.inc_ground r hr_RS).2
          simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, Finset.mem_attach,
            Finset.mem_univ, true_and, SF, R]

      · show ∀ p ∈ RS.rootedsets, p.stem ⊆ A → p.root ∈ A
        --p.stem.card=1であれば作り方から言えそうだが、そうでない場合はどうするか。
        --qの取り方を工夫した方が良かったのかも。ちょっと難しいかも。
        intro p hp hstem
        dsimp [A]
        rw [Finset.mem_biUnion]
        simp
        show ∃ b ∈ q.stem, Relation.ReflTransGen R b p.root

        sorry --ここから帰納法を使う？
        --have h_A_in_SF : SF.sets Aの証明の中。
        --p.rootに辿り着くことができるq.stemの要素が存在することを示せば良い。つまりAの中の元ということ。
        --まだq.root in Aかどうかの場合分け前。Aは言明には直接は出てこないがpの条件として出てくる。
        --登場するのは、qとRとpになる。
        --qは、ステムの大きさが2以上と仮定された根付き集合。
        --pもRSの根付き集合で、stemがAに含まれるもの。
        --Rは、fun x y => ∃ r ∈ RS.rootedsets, y = r.root ∧ r.stem = {x}
        --pのステムの大きさが1であれば、Aの定義からp.rootがAに含まれることは問題ないが、問題はpのステムの大きさが2以上の場合。
        --Aの大きさが最小になるようにqを取るなど、工夫が必要かもしれない。
        --pを改めてqと取り直すと良さそうだが、証明ではどうかけばいいか。
        --pを考えた時にqがまた出てくると巡回してしまう。もっとも下流のものをとりたい。
        --循環するときは、qのステムをhyperedgeが含むことと、pのステムを含むことが同時になる。
        --Aは、hyperedgeが示れば、qのステムのclosureということ。
        --すると、このあとq.rootがAに含まれるかどうかで場合分けするのもおかしいというが自明なケースなのかも。
        --結局、ここで示すことは、qのステムのclosureは、ステムサイズ2のものは考慮せずに1のものだけで計算できるということ。
        --このことを別の補題で示す方針でどうか。
        --ステムサイズ1の集合族では、closureとidealが同値であることはすでに証明済みのような。

    by_cases h_A : q.root ∈ A
    case pos =>
      -- A が q.root を含む場合
      -- すなわち，∃ x ∈ q.stem, R_hat x q.root が成立する
      dsimp [A] at h_A
      rw [Finset.mem_biUnion] at h_A
      obtain ⟨x, hx_in, hR⟩ := h_A
      have : Relation.ReflTransGen R x q.root :=
      by
        dsimp [preorder.R_hat]
        rw [Finset.mem_filter] at hR
        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
          and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const, Subtype.forall,
          Finset.mem_univ, true_and, SF, R, A]
      have :preorder.R_hat R x q.root := by
        exact preorder.ReflTransGen.to_R_hat this

      have s_imp:∀ s :Finset α, SF.sets s→ q.stem ⊆ s → q.root ∈ s := by
        intro s hs hstem
        let rc := rootedpair_compatible (rootedSetsFromSetFamily SF.toSetFamily) s
        have :(rootedsetToClosureSystem (rootedSetsFromSetFamily SF.toSetFamily)).sets s:=
        by
          apply ClosureSystemTheorem SF s hs
        let rc2 := rc this q q_in_RSS hstem
        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
          and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const, Subtype.forall,
          Finset.mem_filter, Finset.mem_univ, and_self, SF, R, A, rc]
      let ta := s_imp A h_A_in_SF h_stem_in_A  --矛盾するかと思ってやったら矛盾せず。
      --R_hat x q.rootがRSのclosureに入るということから攻めるべき。
      --({x},q.root)がRSのclosureに入る。よって、qの極小性に反する。
      have : q.root ∉ ({x.val}:Finset α) :=
      by
        have : q.root ≠ x.val :=
        by
          have xq: x.val ∈ q.stem := by
            simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
              and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const, Subtype.forall,
              Finset.mem_filter, Finset.mem_univ, and_self, Finset.coe_mem, SF, R, A]
          have :q.root ∉ q.stem := by
            exact q.root_not_in_stem
          simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
            and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const, Subtype.forall,
            Finset.mem_filter, Finset.mem_univ, and_self, Finset.coe_mem, SF, R, A]
          obtain ⟨val, property⟩ := x
          simp_all only
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [not_true_eq_false]
        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
          and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const, Subtype.forall,
          Finset.mem_filter, Finset.mem_univ, and_self, Finset.mem_singleton, SF, R, A]


      let v := ValidPair.mk {x.val} q.root this
      have :v ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets :=
      by
        dsimp [rootedSetsFromSetFamily]
        dsimp [rootedSetsSF]
        simp
        dsimp [allCompatiblePairs]
        dsimp [isCompatible]
        simp
        use {x.val}
        use q.root
        constructor
        simp
        simp
        constructor
        · show ({↑x}, q.root) ∈ allPairs SF.toSetFamily
          dsimp [allPairs]
          rw [Finset.product]
          apply Finset.mem_product.mpr

          have SR_ground:SF.ground = (rootedSetsFromSetFamily SF.toSetFamily).ground := by
              simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt,
                forall_exists_index, and_imp, Finset.biUnion_subset_iff_forall_subset,
                Finset.mem_attach, forall_const, Subtype.forall, Finset.mem_filter, Finset.mem_univ,
                and_self]
              obtain ⟨val, property⟩ := x
              simp_all only
              rfl
          constructor
          · show ({↑x}, q.root).1 ∈ SF.ground.powerset
            simp
            let rs1 := ((rootedSetsFromSetFamily SF.toSetFamily).inc_ground q q_in_RSS).1
            let rs1p := rs1 x.property
            rw [SR_ground]
            simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt,
              forall_exists_index, and_imp, Finset.biUnion_subset_iff_forall_subset,
              Finset.mem_attach, forall_const, Subtype.forall, Finset.mem_filter, Finset.mem_univ,
              and_self]
          · show q.root ∈ SF.ground
            let rs2 := ((rootedSetsFromSetFamily SF.toSetFamily).inc_ground q q_in_RSS).2
            rw [SR_ground]
            simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt,
              forall_exists_index, and_imp, Finset.biUnion_subset_iff_forall_subset,
              Finset.mem_attach, forall_const, Subtype.forall, Finset.mem_filter, Finset.mem_univ,
              and_self]
        · constructor
          · show ¬q.root = ↑x
            let qr := q.root_not_in_stem
            simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
              and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const, Subtype.forall,
              Finset.mem_filter, Finset.mem_univ, and_self, SF, R, A]
            obtain ⟨val, property⟩ := x
            simp_all only
            apply Aesop.BuiltinRules.not_intro
            intro a
            subst a
            contradiction
          · show ∀ (t : Finset α), SF.sets t → ↑x ∈ t → q.root ∈ t
            intro t st xt
            show q.root ∈ t
            --ここは、Aがq.rootを含む場合。
            --qの極小性に反して、qより小さいvが存在するので矛盾をいうところのひとつ。
            --vがrootedcircuits_from_RSに含まれることを示す部分。
            --xからRで辿って行ったらq.rootに辿り着いたという状況。
            have : preorder.R_hat R x.val q.root := by
              dsimp [preorder.R_hat]
              rw [Finset.mem_filter] at hR
              simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
                and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const, Subtype.forall,
                Finset.mem_univ, true_and, SF, R, A]
              intro s a a_1
              obtain ⟨val, property⟩ := x
              simp_all only
              apply this
              · simp_all only
              · simp_all only
            --ここからpreorderの定理を使う。
            dsimp [preorder.R_hat] at this
            let pr := preorder.R_hat.to_ReflTransGen this
            let prm := (preorder.mem_S_R_iff R t).mp
            have : t ∈ preorder.S_R R :=
            by
              dsimp [preorder.S_R]
              rw [Finset.mem_filter]
              constructor
              · simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt,
                forall_exists_index, and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach,
                forall_const, Subtype.forall, Finset.mem_filter, Finset.mem_univ, and_self, Finset.powerset_univ, SF,
                R, A, pr]
              · dsimp [preorder.closedUnder]
                dsimp [R]
                intro a b ha hb
                obtain ⟨r, hr_RS, hroot, hstem⟩ := ha
                dsimp [SF] at st
                dsimp [rootedsetToClosureSystem] at st
                dsimp [filteredFamily] at st
                simp at st
                let st2 := st.2 r hr_RS
                have :r.stem ⊆ t := by
                  subst hroot
                  simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero,
                    gt_iff_lt, forall_exists_index, and_imp,
                    Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const,
                    Subtype.forall, Finset.mem_filter, Finset.mem_univ, and_self,
                    Finset.singleton_subset_iff]
                let st3 := st2 this
                rw [←hroot] at st3
                exact st3
            simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt,
              forall_exists_index, and_imp, Finset.biUnion_subset_iff_forall_subset,
              Finset.mem_attach, forall_const, Subtype.forall, Finset.mem_filter, Finset.mem_univ,
              and_self]

      --qの極小性に反して、qより小さいvが存在するので矛盾
      simp_all only [implies_true, not_true_eq_false, SF]
      dsimp [rootedcircuits_from_RS] at hq
      rw [Finset.mem_filter] at hq
      obtain ⟨left, right⟩ := hq
      let rv := right v this
      have: q.root = v.root := by
        simp_all only [not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index, and_imp,
          Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const, Subtype.forall, Finset.mem_filter,
          Finset.mem_univ, and_self, R, A]
      let rv2 := rv this
      have : v.stem = {x.val} := by
        dsimp [v]
      rw [this] at rv2
      have : x.val ∈ q.stem := by
        exact x.property
      --q_ge_1 --: q.stem.card > 1 := by
      have xq_sub: {x.val} ⊆ q.stem := by
        simp
      have : {x.val} ≠ q.stem := by
        intro h_eq
        rw [←h_eq] at q_ge_1
        exact lt_irrefl _ q_ge_1
      have :{x.val} ⊂ q.stem  := by
        exact Finset.ssubset_iff_subset_ne.mpr ⟨xq_sub, this⟩
      contradiction

    case neg =>
      -- A が q.root を含まない場合
      -- すなわち，∀ x ∈ q.stem, ¬ R x q.root が成立する
      --qのstemがAに含まれて、qのrootがAに含まれないが、Aは、RSと両立することが示せるので、
      --矛盾が生じる。
      --SF.sets A と r.stem ⊆ A → r.root ∈ A が成り立つことから、
      let rc := rootedpair_compatible (rootedSetsFromSetFamily SF.toSetFamily) A
      have :rootedsetToClosureSystem (rootedSetsFromSetFamily SF.toSetFamily) = SF :=
      by
        let cr := closuresystem_rootedsets_eq SF
        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
          and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const, Subtype.forall,
          Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists, exists_prop, not_exists,
          not_and, SF, cr, R, A]
      have :(rootedsetToClosureSystem (rootedSetsFromSetFamily SF.toSetFamily)).sets A :=
      by
        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, forall_exists_index,
          and_imp, Finset.biUnion_subset_iff_forall_subset, Finset.mem_attach, forall_const, Subtype.forall,
          Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists, exists_prop, not_exists,
          not_and, SF, R, A]
      let rc2 := rc this q
      have : q ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets := by
        dsimp [rootedcircuits_from_RS] at hq
        rw [Finset.mem_filter] at hq
        exact hq.1
        --circuitsならばねつき集合になるということがすでに証明されているので、それを使う。
        --q ∈ (rootedcircuits_from_RS (rootedSetsFromSetFamily SF.toSetFamily)).rootedsets
      let rc3 := rc2 this h_stem_in_A
      contradiction --rootがAに属するか属さないかの矛盾。

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
