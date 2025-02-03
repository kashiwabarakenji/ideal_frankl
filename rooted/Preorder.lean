import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic
import rooted.CommonDefinition
import rooted.RootedCircuits
import rooted.RootedImplication
import rooted.RootedFrankl
import LeanCopilot

open Classical

variable {α : Type} [DecidableEq α] [Fintype α]

namespace preorder
/-
このo1 namespaceでは、関係 R の推移的閉包 (ReflTransGen R) を、
R に閉じた有限集合の族 S_R を用いて構成することを証明する。

1. `closedUnder R s`: 集合 s が R に閉じていることを表す述語。
2. `S_R R`: R に閉じた有限集合の族を Finset で定義。
3. `R_hat R x y`: すべての s ∈ S_R R に対して x ∈ s ⇒ y ∈ s となる関係。
4. `ReflTransGen.to_R_hat`: 帰納法を用いて ReflTransGen R x y → R_hat R x y を証明。
5. `R_hat.to_ReflTransGen`: 反証法を用い、R_hat R x y → ReflTransGen R x y を証明。
6. `R_hat_iff_ReflTransGen`: 上記の双方向の証明を組み合わせ、両者の同値性を示す。
7. `R_hat_eq_ReflTransGen`: 関係全体として R_hat = ReflTransGen を証明。
8. `S_R` を Finset の powerset と filter を用いて構成し、計算可能性を確保。
9. `R_hat.to_ReflTransGen` では、R に閉じた要素全体を集めた Finset を構成し矛盾を導く。
10. `ReflTransGen.to_R_hat` では帰納法を用い、s が R に閉じていることを利用して証明。

この結果により、推移的閉包は R に閉じた有限集合族の情報から完全に再構成できることが示される。
-/
--------------------------------------------------------------------------------
-- 1. 「有限集合 s が R に閉じている」ことを表す述語 closedUnder R s
--------------------------------------------------------------------------------

/--
`s` が関係 `R` に閉じている:
「もし R x y が成り立つなら、x ∈ s ⇒ y ∈ s」
-/
def closedUnder (R : α → α → Prop) (s : Finset α) : Prop :=
  ∀ ⦃x y : α⦄, R x y → (x ∈ s → y ∈ s)

--------------------------------------------------------------------------------
-- 2. S_R R の定義
--    「α のすべての部分有限集合のうち、R に閉じているもの」
--------------------------------------------------------------------------------

/-
S_R R := { s ∣ s は R に閉じている } を Finset で表現する。イデアルといってもいい。イデアル集合族のイデアルとは意味が異なるが。
-/
noncomputable def S_R (R : α → α → Prop) : Finset (Finset α) :=
  (Finset.univ.powerset).filter (λ s => closedUnder R s)

/-
`s ∈ S_R R` であることと、`s` が R に閉じていることの同値。書き換えといえるか。
-/

omit [DecidableEq α] in
lemma mem_S_R_iff (R : α → α → Prop) (s : Finset α) :
    s ∈ S_R R ↔ closedUnder R s := by
  -- 定義展開: s ∈ filter P X ↔ (s ∈ X ∧ P s)
  simp only [S_R, Finset.mem_filter, Finset.mem_powerset]
  -- s ∈ powerset univ  ↔  s ⊆ univ
  -- ただし s ⊆ univ は常に真なので省略可だが、いちおうきちんと見る
  constructor
  · rintro ⟨hs_subset, h_closed⟩
    exact h_closed
  · intro h
    -- s は `closedUnder R`
    -- powerset の要件: s ⊆ univ, これは自明 (Finset.subset_univ s)
    exact ⟨Finset.subset_univ s, h⟩

--------------------------------------------------------------------------------
-- 3. R_hat の定義
--------------------------------------------------------------------------------

/--
R_hat R x y :=
「すべての s ∈ S_R R に対して、もし x ∈ s なら y ∈ s」
集合族から定義された、2項関係。
-/
def R_hat (R : α → α → Prop) (x y : α) : Prop :=
  ∀ (s : Finset α), s ∈ S_R R → (x ∈ s → y ∈ s)

--------------------------------------------------------------------------------
-- 4. 推移的閉包 ReflTransGen R x y (すでに mathlib 4 に定義あり)
--------------------------------------------------------------------------------
-- ReflTransGen R x y とは
--   x = y (refl)  もしくは
--   x ->* a かつ R a b を1ステップ -> b ->* y (tail)
-- の有限回繰り返しで x から y に到達可能

--------------------------------------------------------------------------------
-- 5(1). ReflTransGen R x y → R_hat R x y
--
--      帰納法を使って示す。ReflTransGenの構造に関する帰納法。
--inductive ReflTransGen (r : α → α → Prop) (a : α) : α → Prop
--  | refl : ReflTransGen r a a
--  | tail {b c} : ReflTransGen r a b → r b c → ReflTransGen r a c
--------------------------------------------------------------------------------

omit [DecidableEq α] in
lemma ReflTransGen.to_R_hat {R : α → α → Prop} {x y : α}
  (h : Relation.ReflTransGen R x y) : R_hat R x y := by
  -- ゴール: ∀ s ∈ S_R R, x ∈ s → y ∈ s
  intro s hs hx
  -- hs: s ∈ S_R R  => closedUnder R s
  -- hx: x ∈ s
  -- h : x から y への有限回の到達 (推移的閉包)
  induction h
  case refl z =>
    -- x = y の場合 (0ステップ到達)
    -- z とは x のこと。x = y なので trivially y ∈ s
    simp_all only
  case tail a b c hab rab ih =>
    -- a から b へ (既に推移的閉包), さらに 1ステップ R b c => a から c
    -- ih: x ∈ s ⇒ b ∈ s
    -- さらに s は R に閉じている => b ∈ s ⇒ c ∈ s
    -- 最終的に x ∈ s ⇒ c ∈ s
    have hb : b ∈ s :=
    by
      simp_all only

    -- mem_S_R_iff で closedUnder へ
    rw [mem_S_R_iff] at hs
    exact hs rab hb

--------------------------------------------------------------------------------
-- 5(2). R_hat R x y → ReflTransGen R x y
--
--      反証法：もし推移的閉包が成り立たないなら、
--      「x から到達可能な要素」だけ集めた finset で矛盾を得る。単項イデアル的なもの。
--------------------------------------------------------------------------------

omit [DecidableEq α] in
lemma R_hat.to_ReflTransGen {R : α → α → Prop} {x y : α}
  (h : R_hat R x y) : Relation.ReflTransGen R x y := by
  by_contra hneg
  -- hneg : ¬ ReflTransGen R x y

  -- s := { z in univ | ReflTransGen R x z } (x から到達可能な要素)
  -- Finset 版: filter univ
  let s : Finset α := Finset.univ.filter (λ z => Relation.ReflTransGen R x z)

  -- (i) s が R に閉じていることを示す => s ∈ S_R R
  have s_closed : closedUnder R s := by
    -- ゴール: ∀ a b, R a b → (a ∈ s → b ∈ s)
    intros a b Rab ha
    -- ha: a ∈ s => つまり a ∈ univ ∧ ReflTransGen R x a が真
    -- b を s に入れたい => b ∈ univ ∧ ReflTransGen R x b
    -- ReflTransGen R x a & R a b => ReflTransGen R x b (tail)
    have : Relation.ReflTransGen R x a := by
      -- a が s に入っている => filter の定義から ReflTransGen R x a が成り立つ
      simp_all only [Finset.mem_filter, Finset.mem_univ, true_and, s]
    apply Finset.mem_filter.2
    constructor
    · -- b ∈ univ は自明
      exact Finset.mem_univ b
    · -- ReflTransGen R x b
      exact Relation.ReflTransGen.tail this Rab

  -- s が R に閉じている => s ∈ S_R R
  have s_in : s ∈ S_R R := by
    rw [mem_S_R_iff]
    exact s_closed

  -- (ii) x ∈ s : x は自分自身に0ステップで到達 => ReflTransGen.refl x
  have hx : x ∈ s := by
    apply Finset.mem_filter.2
    simp_all only [Finset.mem_univ, true_and, s]
    rfl

  -- (iii) y ∉ s : もし y ∈ s なら ReflTransGen R x y が真 (filter の定義上) になってしまうが，
  -- それは hneg と矛盾
  have hy : y ∉ s := fun hy_in =>
    let ⟨_, hy_rel⟩ := Finset.mem_filter.1 hy_in
    hneg hy_rel

  -- (iv) ところが R_hat より，s を代入すれば x ∈ s ⇒ y ∈ s のはず
  --      hx から y ∈ s が出るが hy と矛盾
  apply hy
  exact h s s_in hx

--------------------------------------------------------------------------------
-- 6. R_hat R x y と ReflTransGen R x y は同値
--------------------------------------------------------------------------------

omit [DecidableEq α] in
lemma R_hat_iff_ReflTransGen {R : α → α → Prop} (x y : α) :
    R_hat R x y ↔ Relation.ReflTransGen R x y :=
  ⟨R_hat.to_ReflTransGen, ReflTransGen.to_R_hat⟩

--------------------------------------------------------------------------------
-- 7. 関係としての一致: R_hat R = ReflTransGen R
--    （x y を一つずつみたとき同値なので、関係全体としても同じ）
--------------------------------------------------------------------------------

omit [DecidableEq α] in
theorem R_hat_eq_ReflTransGen (R : α → α → Prop) :
    R_hat R = Relation.ReflTransGen R := by
  funext x
  funext y
  apply propext (R_hat_iff_ReflTransGen x y)


/-
このPropVersion namespaceでは、関係 R の反射推移的閉包 (star R) を形式的に定義し、
有限回の経路を考えることで、S(R) の構造が変化しないことを証明する。

1. `star R x y` は、x から y へ R を有限回たどって到達できることを表す。
   - `refl x` : x → x（0ステップ）
   - `tail rxy hyz` : R x y かつ star R y z ならば star R x z
2. `pathOfLength R x y n` は、ちょうど n 回の R-ステップで x から y へ到達することを表す。
3. `star_implies_pathExists` では、star R x y が成り立つとき、有限ステップのパスが存在することを証明。
4. `pathOfLength.induce` により、R で閉じた集合では、有限ステップの各要素が属することを示す。
5. `S(R)` は R に閉じた有限集合族を定義し、Finset の filter を用いて構築。
6. `S_eq_S_star` では、R の推移的閉包をとっても S(R) は変化しないことを証明。
   - star R x y を用いて S(R) の条件が維持されることを示す。
   - R に閉じた集合族が star R に対しても閉じていることを確認。

この結果により、推移的閉包を考慮しても R に閉じた集合族の構造が変化しないことが示される。
-/
/--
  反射推移的閉包 (reflexive transitive closure) を表す命題。
  `star R x y` は「x から y へ R を有限回たどって到達できる」という意味。

  - `refl x` : 0ステップで x→x
  - `tail rxy hyz` : R x y が成り立ち、かつ y→z の有限ステップ到達 (star R y z)
    があるなら、x→z の有限ステップ到達が得られる
-/
inductive star {α : Type} (R : α → α → Prop) : α → α → Prop
| refl (x : α) : star R x x
| tail {x y z : α} : R x y → star R y z → star R x z

open star

/--
  「ちょうど n 回の R-ステップで x から y に到達する」という命題。
  データ構造ではなく、論理命題として定義する (`: Prop`)。
-/
inductive pathOfLength {α : Type} (R : α → α → Prop) : α → α → Nat → Prop
| zero (x : α) : pathOfLength R x x 0
| succ {x y z : α} {n : Nat} :
    R x y → pathOfLength R y z n → pathOfLength R x z (n+1)

/--
  `star R x y` が成り立つとき、
  「ある自然数 n が存在して、n ステップの R-パスで x から y へ行ける」
  という事実 (∃ n, pathOfLength R x y n) を示す補題（存在証明）。
-/
lemma star_implies_pathExists {α : Type} {R : α → α → Prop}
  (x y : α) (hxy : star R x y) :
  ∃ (n : Nat), pathOfLength R x y n := by
  -- `induction hxy` でケース分け
  induction hxy
  case refl w =>
    /-
      「refl w」の場合、型は `star R w w`。
       つまり、このとき x = w, y = w のはず。
       しかし Lean は自動では x= w, y= w とみなしてくれないので、subst で消し込む。
    -/
    -- ここでゴールが「∃ (n : ℕ), pathOfLength R w w n」に化簡される
    exists 0
    exact pathOfLength.zero w

  case tail x' y' z' rxy hyz ih =>
    -- ここで ih : ∃ n, pathOfLength R y' z' n
    let ⟨n, p⟩ := ih
    exists (n+1)
    exact pathOfLength.succ rxy p


/--
  補題：`pathOfLength R x y n` が成り立つとき、もし s が「R で閉じている」集合
      (すなわち ∀ a b, R a b → (a ∈ s → b ∈ s))
  であれば x ∈ s から y ∈ s が導ける。
  これは「有限列の各ステップで要素が s に属したまま移動する」ことを帰納的に言っている。
-/
lemma pathOfLength.induce
  {α : Type} {R : α → α → Prop} {s : Finset α}
  (sClosed : ∀ {a b}, R a b → a ∈ s → b ∈ s) :
  ∀ {x y n}, pathOfLength R x y n → (x ∈ s → y ∈ s)
:= by
  -- まず x, y, n, p (pathOfLength R x y n の証明) と「x ∈ s」を仮定に取り込む
  intros x y n p hx
  -- p : pathOfLength R x y n を帰納的に処理
  induction p
  case zero w =>
    -- case zero w は「p = pathOfLength.zero w」で、x=y=w の0ステップパス。
    -- x ∈ s ⇒ y ∈ s は「hx ⇒ hx」となってそのまま完了
    exact hx

  case succ x' y' z' m rxy pyz ih =>
    /-
      この枝では
        p = pathOfLength.succ rxy pyz
        x'=x, z'=y, n=m+1
      が文脈にある。
      rxy : R x y'
      pyz : pathOfLength R y' y m
      ih  : (y' ∈ s → y ∈ s) という再帰仮定
    -/
    let hy := sClosed rxy hx
    -- y' ∈ s であれば y ∈ s とわかるので、hx から rxy により y' ∈ s
    exact ih hy

/-
  集合族 S(R) の定義：
  S(R) = { s | ∀ x y, R x y → (x ∈ s → y ∈ s) }.
-/

--上のS_Rと被っている。Sに統一した。--
--noncomputable def S {α : Type} [Fintype α] (R : α → α → Prop) : Finset (Finset α) :=
--  (Finset.univ).filter (λ s => ∀ ⦃x y : α⦄, R x y → (x ∈ s → y ∈ s))

/--
  メイン定理：
  有限集合 α 上の反射的な関係 R について、その反射推移的閉包 star R をとっても、
  S(R) と S(star R) は一致する (S R = S (star R))。
-/
theorem S_eq_S_star
  {α : Type}[Fintype α] (R : α → α → Prop)
  --(hRefl : ∀ x, R x x)  -- R が反射的（問題文の仮定）
  : S_R R = S_R (star R)
:= by
  apply Finset.ext
  intro s
  apply Iff.intro
  -------------------------------------------------------------------------
  -- (1) s ∈ S(R) ⇒ s ∈ S(star R)
  -------------------------------------------------------------------------
  · intro hs  -- hs: s が R に閉じている
    dsimp [S_R] at hs
    rw [Finset.mem_filter] at hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, fun {x y} (hxy : star R x y) (hx : x ∈ s) =>
      -- star_implies_pathExists で「∃ n, pathOfLength R x y n」を取り出す
      let ⟨n, p⟩ := star_implies_pathExists x y hxy
      -- pathOfLength.induce を用いて x ∈ s ⇒ y ∈ s を示す
      pathOfLength.induce (fun {a b} rab => hs.2 rab) p hx⟩

  -------------------------------------------------------------------------
  -- (2) s ∈ S(star R) ⇒ s ∈ S(R)
  -------------------------------------------------------------------------
  · intro hs' -- hs': s が star R に対して閉じている
    dsimp [S_R] at hs'
    rw [Finset.mem_filter] at hs'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, fun {x y} (rxy : R x y) (hx : x ∈ s) =>
        -- R x y ならば、star.tail rxy (star.refl y) により star R x y が成り立つ
        -- よって s が star R に閉じている性質から y ∈ s
        hs'.2 (star.tail rxy (star.refl y)) hx
      ⟩ -- Finset.mem_filter.mpr で「∀ x y, R x y → (x ∈ s → y ∈ s)」を示す

-- S(R) = S(R') を別証明。推移的閉包の作る集合族と、推移的閉包を考えずに作る集合族は同じ集合族。
--o1.R_hat_eq_ReflTransGenの定理を利用した証明。
omit [DecidableEq α] in
theorem S_eq_S_star_fromR (R : α → α → Prop) :
  S_R R = S_R (Relation.ReflTransGen R) := by
  rw [← R_hat_eq_ReflTransGen]  -- R' R を R_hat(S R) に置き換え
  apply Finset.ext  -- 集合の等号を示すには extensionality を使う
  intro s
  apply Iff.intro
  · intro hs
    dsimp [S_R] at hs
    dsimp [S_R]
    simp at hs
    simp
    dsimp [closedUnder]
    dsimp [R_hat]
    dsimp [S_R]
    intro x y hxy hx
    simp_all only [Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and]
    --exact hxy _ hs hx

  · intro hs
    dsimp [S_R] at hs
    dsimp [S_R]
    simp
    simp at hs
    dsimp [closedUnder] at hs
    dsimp [R_hat] at hs
    dsimp [S_R] at hs
    intro x y hxy hx
    simp_all only [Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and]
    apply hs
    intro s_1 a a_1
    apply a
    on_goal 4 => {exact hx
    }
    on_goal 2 => {exact a_1
    }
    · simp_all only



/-
1. **`down_closure S` の定義**
   \( S \) の各要素 \(s\) に対して、\( s \) より小さい（またはイコール）元をすべて集めて合併しています。
2. **共通部分への包含 (前半の `· intro x hx ...`)**
   \( x \) が `down_closure S` に属するとき、任意の「\( S \subseteq D \) かつ down set」\( D \) へ必ず属することを示しています。
3. **共通部分からの包含 (後半の `· intro xx hx ...`)**
   \( xx \) が「\( S \subseteq D \) かつ down set」のすべてに属するならば、あらかじめ構成したダウンセット \( D' \) にも属するので、そこから \( xx \) が `down_closure S` に属することを結論づけています。
-/

variable {P : Type*} [Preorder P][Fintype P][DecidableEq P]

-- 定義: S の down set 閉包 (S が生成する down set)
noncomputable def down_closure (S : Finset P) : Finset P :=
  S.biUnion (fun s => (Finset.univ.filter (fun x => x ≤ s)))

-- Preorderを前提として、Sから辿れる集合と、Sを含むideal全体の共通部分が等しくなる。
lemma down_closure_eq_Inf (S : Finset P) :
  down_closure S = (Finset.univ.filter (fun D => S ⊆ D ∧ ∀ x ∈ D, ∀ y, y ≤ x → y ∈ D)).inf id := by
  apply Finset.Subset.antisymm
  -- down_closure S は共通部分に含まれることを示す
  · intro x hx
    rw [Finset.mem_inf]
    simp
    intro s hs hh
    dsimp [down_closure] at hx
    dsimp [Finset.biUnion] at hx
    simp at hx
    obtain ⟨w, h⟩ := hx
    obtain ⟨left, right⟩ := h
    exact hh _ (hs left) _ right

  -- 共通部分は down_closure S に含まれることを示す
  · intro xx hx
    rw [Finset.mem_inf] at hx
    simp at hx
    -- 任意の down set D (S ⊆ D) について xx ∈ D である。
    -- ここで、D' を「S を含む down set」として構成し、xx ∈ D' から結論を得る。
    let D' := S.biUnion (fun s => Finset.univ.filter (fun z => z ≤ s))
    have D'_in_filter : D' ∈ Finset.univ.filter (fun D => S ⊆ D ∧ ∀ x ∈ D, ∀ y, y ≤ x → y ∈ D) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      constructor
      · -- S ⊆ D' を示す
        intro a ha
        apply Finset.mem_biUnion.mpr
        exact ⟨a, ha, by simp [ha]⟩
      · -- D' が down set であることを示す
        intro x hxD' y hyx
        obtain ⟨s, hsS, hxFilt⟩ := Finset.mem_biUnion.mp hxD'
        rw [Finset.mem_filter] at hxFilt
        obtain ⟨_, hxLe⟩ := hxFilt
        have : y ≤ s := le_trans hyx hxLe
        apply Finset.mem_biUnion.mpr
        exact ⟨s, hsS, by simp [this]⟩

    -- xx はその交わり (inf) の要素なので、D' にも属する
    have xx_in_D' : xx ∈ D' :=
    by
      dsimp [down_closure]
      apply Finset.mem_biUnion.mpr
      simp

      by_contra h_not
      have not_in: xx ∉ down_closure S := by
        dsimp [down_closure]
        dsimp [Finset.biUnion]
        simp
        push_neg at h_not
        exact h_not

      have : down_closure S ∈ Finset.univ.filter (fun D => S ⊆ D ∧ ∀ x ∈ D, ∀ y, y ≤ x → y ∈ D) :=
      by
        simp_all only [Finset.mem_filter, Finset.mem_univ, Finset.mem_biUnion, true_and, forall_exists_index, and_imp,
          not_exists, not_and, D']
        obtain ⟨left, right⟩ := D'_in_filter
        apply And.intro
        · exact left
        · intro x a y a_1
          dsimp [down_closure] at a
          dsimp [down_closure]
          simp_all only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          obtain ⟨w, h⟩ := a
          obtain ⟨left_1, right_1⟩ := h
          apply right
          on_goal 3 => {exact a_1
          }
          on_goal 2 => {exact right_1
          }
          · simp_all only

      simp_all only [Finset.mem_filter, Finset.mem_univ, Finset.mem_biUnion, true_and, forall_exists_index, and_imp,
        not_exists, not_and, D']
      obtain ⟨left, right⟩ := D'_in_filter
      obtain ⟨left_1, right_1⟩ := this
      apply h_not
      · apply hx
        · simp_all only [subset_refl]
        · intro x a y a_1
          tauto
      · simp_all only [le_refl]

    -- xx ∈ S.biUnion (...) なので、xx ≤ s を満たす s ∈ S を得る
    dsimp [down_closure]
    dsimp [Finset.biUnion]
    simp
    obtain ⟨s, hsS, hxxs⟩ := Finset.mem_biUnion.mp xx_in_D'
    rw [Finset.mem_filter] at hxxs
    obtain ⟨_, hxx_le_s⟩ := hxxs
    exact ⟨s, hsS, hxx_le_s⟩

end preorder
