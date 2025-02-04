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
import rooted.ClosureOperator
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

--デバッグのために補題を外に出す。別の補題でも役に立った。
lemma nonempty_filtered_powerset {α : Type} [DecidableEq α] [Fintype α] (RS : RootedSets α)  [DecidablePred (rootedsetToClosureSystem RS).sets] (s : Finset RS.ground) :
  let SF := rootedsetToClosureSystem RS
  (Finset.filter (fun t => SF.sets t ∧ Finset.image Subtype.val s ⊆ t) RS.ground.powerset).Nonempty :=
by
  intro SF
  use RS.ground
  simp
  constructor
  · exact SF.has_ground
  · show Finset.image Subtype.val s ⊆ RS.ground
    rw [Finset.image_subset_iff]
    intro x_1 a
    simp_all only [Finset.coe_mem]

--preorderのところにあるdown_closure_eq_Infの集合続版。preorderのほうの定理を利用しても証明できると思われるが、直接証明する。
lemma preorder_ideal_lemma {α : Type} [DecidableEq α] [Fintype α]
  (RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
  (h₁ : ∀ p ∈ RS.rootedsets, p.stem.card = 1) :
  let SF := rootedsetToClosureSystem RS
  ∀ s : Finset RS.ground,
  (preorder_ideal RS s).image Subtype.val = finsetIntersection (RS.ground.powerset.filter (fun (t : Finset α) => SF.sets t ∧ (s.image Subtype.val) ⊆ t)) :=
by
  intro SF s --sはhyperedgeとは限らない。
  ext ss --左右の集合族からとってきた集合。
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
    --デバッグのために証明を外に出した。
    have h_assume: (Finset.filter (fun t => SF.sets t ∧ Finset.image Subtype.val s ⊆ t) RS.ground.powerset).Nonempty :=
    by
      exact nonempty_filtered_powerset RS s
    --ここがエラーなわけでもなさそう。
    have mf := mem_finsetIntersection_iff_of_nonempty (RS.ground.powerset.filter (fun (t : Finset α) => SF.sets t ∧ (s.image Subtype.val) ⊆ t))

    rw [mf ss h_assume] at hsss
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
    swap --placeholder errorを回避するために追加
    · simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, forall_const, subset_refl, SF]
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
      have ssp: SF.sets ((preorder_ideal RS s).image Subtype.val):=
      by
        exact preorder_ideal_closed RS h₁ s
      let hssss := hsss ((preorder_ideal RS s).image Subtype.val) pig ssp s_in_ideal
      rw [Finset.mem_image] at hssss
      obtain ⟨a, ha, rfl⟩ := hssss
      exact ha

--いままで証明したことを利用するだけなので、証明がもっと短く書けるかもしれない。
lemma size_one_preorder_closure {α : Type} [DecidableEq α] [Fintype α]
  (RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
  (h₁ : ∀ p ∈ RS.rootedsets, p.stem.card = 1) :
  let SF := rootedsetToClosureSystem RS
  ∀ s : Finset RS.ground, closureOperator SF s = preorder_ideal RS s :=
by
  intro SF s
  let pil := preorder_ideal_lemma RS h₁ s
  have : preorder_ideal RS s = (finsetIntersection (Finset.filter (fun t => (rootedsetToClosureSystem RS).sets t ∧ Finset.image Subtype.val s ⊆ t) RS.ground.powerset)).subtype (fun x=> x ∈ RS.ground):=
  by
    rw [←pil]
    ext y
    apply Iff.intro
    · intro h
      simp at h
      simp
      exact h
    · intro h
      simp at h
      simp_all only
  rw [this]

  ext x
  constructor
  · intro hx
    rw [mem_closure_iff_lemma] at hx
    simp
    rw [mem_finsetIntersection_iff_of_nonempty]
    · intro f hf
      have :s ⊆ Finset.subtype (fun x => x ∈ SF.ground) f :=
      by
        simp_all only [Finset.mem_filter, Finset.mem_powerset, SF]
        obtain ⟨left, right⟩ := hf
        obtain ⟨left_1, right⟩ := right
        intro x hx
        simp_all only [Finset.mem_subtype]
        obtain ⟨val_1, property_1⟩ := x
        apply right
        simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const]
      let hxf := hx (Finset.subtype (λ x => x ∈ SF.ground) f) this
      have :SF.sets (Finset.image Subtype.val (Finset.subtype (fun x => x ∈ SF.ground) f)):=
      by
        simp_all only [Finset.mem_filter, Finset.mem_powerset, SF]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := hf
        obtain ⟨left_1, right⟩ := right
        convert left_1
        ext a : 1
        simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
          exists_eq_right_right, and_iff_left_iff_imp]
        intro a_1
        exact left a_1

      let fxf2 := hxf this

      simp_all only [Finset.mem_filter, Finset.mem_powerset]
      obtain ⟨val, property⟩ := x
      obtain ⟨left, right⟩ := hf
      obtain ⟨left_1, right⟩ := right
      simp_all only
      simpa using fxf2

    · show (Finset.filter (fun t => (rootedsetToClosureSystem RS).sets t ∧ Finset.image Subtype.val s ⊆ t) RS.ground.powerset).Nonempty
      exact nonempty_filtered_powerset RS s

  · intro hx
    simp at hx
    rw [mem_finsetIntersection_iff_of_nonempty] at hx
    swap
    exact nonempty_filtered_powerset RS s

    rw [mem_closure_iff_lemma]
    intro f hf
    intro sfs
    have :Finset.image Subtype.val f ∈ (Finset.filter (fun t => (rootedsetToClosureSystem RS).sets t ∧ Finset.image Subtype.val s ⊆ t) RS.ground.powerset) :=
    by
      simp_all only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      swap
      ·
        simp_all only [and_imp, true_and, SF]
        obtain ⟨val, property⟩ := x
        simp_all only
        simp_all only [SF]
        rw [Finset.image_subset_iff]
        intro x a
        simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
          Finset.coe_mem, exists_const]
        obtain ⟨val_1, property_1⟩ := x
        exact hf a
      · simp_all only [and_imp, SF]
        obtain ⟨val, property⟩ := x
        simp_all only
        simp_all only [SF]
        simp [Finset.image_subset_iff]

    let hxf := hx (f.image Subtype.val) this
    simp_all only [SF]
    obtain ⟨val, property⟩ := x
    simp_all only [SF]
    rw [Finset.mem_image] at hxf
    simp_all only [Finset.mem_filter, Finset.mem_powerset, true_and, and_imp, Subtype.exists, exists_and_right,
      exists_eq_right, exists_true_left, SF]

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

--rootedcircuitsはここでは、ステムが包含関係極小のものがRSに存在するかでは、なくて、SFから作った極小なものが存在するかであることに注意。
--ステムサイズ1で生成される集合族は、rooted circuitsもステムサイズが1である。
theorem size_one_rooted_circuits [Fintype α](RS : RootedSets α) [DecidablePred (rootedsetToClosureSystem RS).sets]
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

  have qrg : q.root ∈ RS.ground := by
    exact ((rootedSetsFromSetFamily SF.toSetFamily).inc_ground q q_in_RSS).2

  have qsg:q.stem ⊆ RS.ground := by
      intro x hx
      exact ((rootedSetsFromSetFamily SF.toSetFamily).inc_ground q q_in_RSS).1 hx

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

    let A := preorder_ideal RS (q.stem.subtype (fun x => x ∈ RS.ground))

    have h_stem_in_A : q.stem ⊆ A.image Subtype.val:=
    by
      dsimp [A]
      let pe := preorder_extensive RS (q.stem.subtype (fun x => x ∈ RS.ground))
      intro x hx
      simp
      have : x ∈ RS.ground := by
        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, SF]
        exact qsg hx
      use this

      simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, SF]
      apply pe
      simp_all only [Finset.mem_subtype]

    have h_A_in_SF : SF.sets (A.image Subtype.val) :=
    by
      exact preorder_ideal_closed RS h₁ (q.stem.subtype (fun x => x ∈ RS.ground))

    have root_in_A : q.root ∈ A.image Subtype.val :=
    by
      dsimp [A]
      simp
      let rsc :=root_stem_closure SF q q_in_RSS
      simp at rsc
      dsimp [rootedpair_to_subtype] at rsc

      use qrg
      rw [←size_one_preorder_closure RS h₁]

      have :⟨q.root,qrg⟩ ∈ closureOperator SF (Finset.subtype (fun x => x ∈ RS.ground) q.stem):=
      by
        exact rsc
      simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, SF, A]

    --このあと、q.stemの中にその点からスタートして、q.rootへの有向パスが存在することを示す。

    have :⟨q.root, qrg⟩ ∈ preorder_ideal RS (Finset.subtype (fun x => x ∈ RS.ground) q.stem) :=
    by
      simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, Finset.mem_image,
        Subtype.exists, exists_and_right, exists_eq_right, exists_true_left, SF, A]

    let fsi := find_source_of_ideal_element RS (q.stem.subtype (fun x => x ∈ RS.ground)) ⟨q.root, qrg⟩ this
    obtain ⟨z,hz⟩ := fsi

    have z_notin_stem: q.root ∉ ({z.val}:Finset α) :=
    by
      have: q.root ∉ q.stem := by
        exact q.root_not_in_stem
      simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, Finset.mem_image,
        Subtype.exists, exists_and_right, exists_eq_right, exists_const, Finset.mem_subtype, Finset.mem_singleton, SF,
        A]
      obtain ⟨val, property⟩ := z
      obtain ⟨left, right⟩ := hz
      simp_all only
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [not_true_eq_false]
    let v := (ValidPair.mk {z.val} q.root z_notin_stem)
    have size1rooted: v ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets :=
    by
      let hz2 := hz.2
      dsimp [rootedSetsFromSetFamily]
      dsimp [rootedSetsSF]
      dsimp [allCompatiblePairs]
      rw [Finset.mem_image]
      have : preorder.R_hat (R_from_RS1 RS) z ⟨q.root, qrg⟩ := by
        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, Finset.mem_image, Subtype.exists,
        exists_and_right, exists_eq_right, exists_const, SF, A]

      have hsss: ∀ s:Finset { x // x ∈ RS.ground }, (s ∈ (preorder.S_R (R_from_RS1 RS))) → z ∈ s → ⟨q.root,qrg⟩ ∈ s := by
        intro s hs hz_in_s
        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, Finset.mem_image,
          Subtype.exists, exists_and_right, exists_eq_right, exists_const, SF, A]
        obtain ⟨val, property⟩ := z
        obtain ⟨left, right⟩ := hz
        apply hz2
        · simp_all only
        · simp_all only

      have comp: ∀ s:Finset { x // x ∈ RS.ground }, (SF.sets (s.image Subtype.val)) → z ∈ s → ⟨q.root,qrg⟩ ∈ s :=
      by
        intro s hs hz_in_s
        let sop := size_one_preorder_lemma RS h₁ s
        rw [sop] at hs
        exact this s hs hz_in_s

      simp
      use v.stem
      use v.root
      constructor
      · simp_all only [Finset.mem_singleton]
      · dsimp [isCompatible]
        simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, Finset.mem_image,
          Subtype.exists, exists_and_right, exists_eq_right, exists_const, Finset.singleton_subset_iff, true_and, SF,
          A]
        obtain ⟨val, property⟩ := z
        obtain ⟨left, right⟩ := hz
        simp_all only
        apply And.intro
        · dsimp [allPairs]
          dsimp [rootedsetToClosureSystem]
          rw [Finset.product]
          apply Finset.mem_product.mpr
          constructor
          · simp_all only [Finset.mem_powerset, Finset.singleton_subset_iff]
          · simp_all only [Finset.mem_powerset, Finset.singleton_subset_iff]
        · intro t a a_1
          have :(rootedsetToClosureSystem RS).sets (Finset.image Subtype.val (Finset.subtype (fun x => x ∈ RS.ground) t)) :=
          by
            have : t ⊆ RS.ground := by
              let rtc := (rootedsetToClosureSystem RS).inc_ground t a
              exact rtc
            have : Finset.image Subtype.val (Finset.subtype (fun x => x ∈ RS.ground) t) = t :=
            by
              ext a_2 : 1
              simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
                exists_eq_right_right, and_iff_left_iff_imp]
              intro a_3
              exact this a_3
            rw [←this]
            let cst := ClosureSystemTheorem SF t a
            simp_all only

          let comp2 := comp (t.subtype (fun x => x ∈ RS.ground)) this
          have : ⟨val, property⟩ ∈ Finset.subtype (fun x => x ∈ RS.ground) t := by
            simp_all only [Finset.mem_subtype]
          let comp3 := comp2 this
          simpa using comp3

    have zq_sub: {z.val} ⊆ q.stem := by
      simp_all only [implies_true, not_false_eq_true, ne_eq, Finset.card_eq_zero, gt_iff_lt, Finset.mem_image,
        Subtype.exists, exists_and_right, exists_eq_right, exists_const, Finset.mem_subtype,
        Finset.singleton_subset_iff, SF, A]
    have : {z.val} ≠ q.stem := by
      intro h_eq
      rw [←h_eq] at q_ge_1
      exact lt_irrefl _ q_ge_1
    have vq_stem: v.stem  ⊂ q.stem  := by
      exact Finset.ssubset_iff_subset_ne.mpr ⟨zq_sub, this⟩
    dsimp [rootedcircuits_from_RS] at hq
    rw [Finset.mem_filter] at hq
    have : q.root = v.root := by
      simp
    let hqq := hq.2 v size1rooted this

    contradiction --直接矛盾を導く方がよい。
    --transitivityより、rootedpairで、一歩でその点からq.rootへ行ける。qの極小性と矛盾。

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
