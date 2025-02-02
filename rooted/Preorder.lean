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
lemma mem_S_R_iff {R : α → α → Prop} {s : Finset α} :
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

/--
  集合族 S(R) の定義：
  S(R) = { s | ∀ x y, R x y → (x ∈ s → y ∈ s) }.
-/

noncomputable def S {α : Type} [Fintype α] (R : α → α → Prop) : Finset (Finset α) :=
  (Finset.univ).filter (λ s => ∀ ⦃x y : α⦄, R x y → (x ∈ s → y ∈ s))

/--
  メイン定理：
  有限集合 α 上の反射的な関係 R について、その反射推移的閉包 star R をとっても、
  S(R) と S(star R) は一致する (S R = S (star R))。
-/
theorem S_eq_S_star
  {α : Type}[Fintype α] (R : α → α → Prop)
  --(hRefl : ∀ x, R x x)  -- R が反射的（問題文の仮定）
  : S R = S (star R)
:= by
  apply Finset.ext
  intro s
  apply Iff.intro
  -------------------------------------------------------------------------
  -- (1) s ∈ S(R) ⇒ s ∈ S(star R)
  -------------------------------------------------------------------------
  · intro hs  -- hs: s が R に閉じている
    dsimp [S] at hs
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
    dsimp [S] at hs'
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
  S R = S (Relation.ReflTransGen R) := by
  rw [← R_hat_eq_ReflTransGen]  -- R' R を R_hat(S R) に置き換え
  apply Finset.ext  -- 集合の等号を示すには extensionality を使う
  intro s
  apply Iff.intro
  · intro hs
    dsimp [S] at hs
    dsimp [S]
    simp at hs
    simp
    dsimp [R_hat]
    dsimp [S_R]
    intro x y hxy hx
    simp_all only [Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hxy _ hs hx

  · intro hs
    dsimp [S] at hs
    dsimp [S]
    simp
    simp at hs
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

end preorder
-------------
/-
namespace FiniteReconstruction

variable {α : Type} (R : α → α → Prop) [Fintype α] [DecidableEq α]
variable (R : α → α → Prop)
/-
  有限集合 `α` であることを仮定：
  - `[DecidableEq α]`: 要素同定可能
  - `[Fintype α]`   : 有限集合
-/

/-
  R : α → α → Prop は α 上の 2 項関係
-/


/-
  集合族 S(R) の定義：
  S(R) = { s | ∀ x y, R x y → (x ∈ s → y ∈ s) }.

  「R による 1 ステップ閉包を満たす部分集合」の族と考えられる。
-/
noncomputable def S (R : α → α → Prop) : Finset (Finset α) :=
  { s | ∀ ⦃x y : α⦄, R x y → x ∈ s → y ∈ s }

/--
  R' R は R の推移的閉包：
  `Relation.TransGen R x y` は「有限回 R をたどって x から y に行ける」という命題。
-/
def R' (R : α → α → Prop) : α → α → Prop :=
  Relation.ReflTransGen R

/--
  R_hat(S(R)) x y とは、
  「S(R) に属する任意の集合 s で、x ∈ s ならば y ∈ s」
  という性質を満たすかどうかの二項関係。
-/
def R_hat (S_R : Finset (Finset α)) : α → α → Prop :=
  fun x y => ∀ s ∈ S_R, x ∈ s → y ∈ s

/--
  R_hat(S_R) が推移的であることは直接示せる。
-/
lemma R_hat_transitive (S_R : Finset (Finset α)) :
  ∀ x y z, R_hat S_R x y → R_hat S_R y z → R_hat S_R x z := by
  intro x y z hxy hyz s hs hx
  apply hyz s hs (hxy s hs hx)

/--
  **メイン定理**:
  有限集合 α 上の 2 項関係 R に対して、
  R の推移的閉包 R' R は、S(R) から定義される R_hat(S(R)) とちょうど同じ関係になる。

  すなわち ∀ x y, (R' R x y) ↔ (R_hat (S R) x y).
-/
theorem R'_eq_Rhat :
  R' R = R_hat (S R) := by
  -- 二つの関係が同値であることを「x,y 任意」として示すため、ext で展開
  ext x y
  apply Iff.intro

  --------------------------------------------------
  -- (1) R' R x y  →  R_hat (S R) x y
  --------------------------------------------------
  case mp =>
    intro hxy
    -- hxy: Relation.TransGen R x y  (≒ R' R x y)
    induction hxy with
    | refl =>
      --rename_i b
      -- 1ステップ (x→y) の場合: R x y
      -- R_hat(S(R)) x y を示したい
      -- 具体的には「∀ s ∈ S(R), x ∈ s → y ∈ s」を示す
      intro s hs hx
      dsimp [S] at hs
      rw [Finset.mem_filter] at  hs
      simp_all only [Finset.mem_univ, true_and]

    | tail rxy h_xz IH =>
      -- 多ステップ (x→z) は, x→y の 1ステップ + y→z の再帰
      intro s hs hx
      dsimp [S] at hs
      rw [Finset.mem_filter] at hs
      apply hs.2
      on_goal 2 => apply IH
      · simp_all only
      · dsimp [S]
        simp_all only [Finset.mem_univ, true_and, Finset.mem_filter]
        intro x_1 y_1 a a_1
        exact hs a a_1
      · simp_all only

  --------------------------------------------------
  -- (2) R_hat (S R) x y  →  R' R x y
  --------------------------------------------------
  case mpr =>
    intro hxy
    -- 背理法: 「R_hat(S(R)) x y」 だが 「R' R x y」が成り立たない
    by_contra not_xy
    /-
      not_xy : ¬ R' R x y
      hxy    : ∀ s ∈ S(R), (x ∈ s → y ∈ s)

      ここで、「x を含むが y は含まない」かつ「R'R に閉じている (s ∈ S(R'R))」
      ような部分集合 s を集めた族の中で極大要素を取れば矛盾が導ける。
    -/
    let Family :Finset (Finset α):= { s : Finset α | s ∈ S (R' R) ∧ x ∈ s ∧ y ∉ s }

    /-
      **補題**: Family が空でないなら、その中で包含関係 (⊆) で極大な要素が存在する。

      具体的には有限集合上で「要素数が最大」な集合をとればよい。
      ここでは Finset.maxBy を利用。
    -/
    have existsMaxFamily : ∃ s, s ∈ Family ∧ ∀ t ∈ Family, s ⊆ t → s = t := by
      -- allSubs : α の全部分集合を列挙した Finset
      let allSubs := (Finset.univ : Finset α).powerset
      -- cand : 「Family に属する」集合をフィルタしたもの

      --simp_all only [Finset.sep_and, Finset.mem_inter_iff, Finset.mem_setOf_eq, and_imp, true_and, Family]

      let cand := allSubs.filter (fun fset =>
        let S' := (fset : Finset α)
        S' ∈ S (R' R) ∧ x ∈ S' ∧ y ∉ S'
      )
      -- cand が空かどうかで場合分け
      --haveI : LinearOrder (Finset α) := Finset.lex.linearOrder
      by_cases cEmpty : cand = ∅
      case pos =>
        /-
          cand = ∅ の場合:
          「R'R に閉じ, x を含むが y は含まない集合」がそもそも存在しない。
          すると以下のように矛盾を導ける:
        -/
        -- 「x から y への経路が無い」と仮定しているが、
        -- もし全ての s ∈ S(R'R) が x ∈ s なら y ∈ s になってしまうなら、
        -- `R_hat(S(R'R)) x y` が成り立ち、推移的閉包の定義から R'R x y が言えて矛盾。
        -- ここをきちんと書き下す:
        --   「cand = ∅」 ⇒ 「(∀ s, s ∈ S(R'R) → x ∈ s → y ∈ s)」 ⇒ R_hat(S(R'R)) x y ⇒ R'R x y
        --   で contradict not_xy

        -- まず「∀ s, s ∈ S(R'R) → x ∈ s → y ∈ s」を示す
        have : ∀ s, s ∈ S (R' R) → x ∈ s → y ∈ s := by
          intro s hs hx_s
          by_contra hy_s
          -- もし y ∉ s なら s が cand に入るはずだが、cand = ∅
          have s_family : s ∈ Family := by
            dsimp [Family]
            rw [Finset.mem_filter]
            constructor
            simp_all only [Finset.powerset_univ, Finset.mem_univ, cand, allSubs]
            constructor
            simp_all only [Finset.powerset_univ, cand, allSubs]
            constructor
            simp_all only [Finset.powerset_univ, cand, allSubs]
            simp_all only [Finset.powerset_univ, not_false_eq_true, cand, allSubs]

          -- これは cand によるフィルタ定義と一致
          have s_in_cand : s ∈ cand
          apply Finset.mem_filter.2
          constructor
          · apply Finset.mem_powerset.2
            apply Finset.subset_univ
          · intro S'
            simp_all only [Finset.powerset_univ, Finset.not_mem_empty, cand, allSubs, Family]
          simp_all only [Finset.powerset_univ, Finset.not_mem_empty, cand, allSubs, Family]
        -- つまり「R_hat (S(R'R)) x y」が成り立った
        -- すると多ステップの性質から R'R x y が示せる（TransGen理論上）
        -- しかし not_xy : ¬ R' R x y と矛盾
        -- ここはもう直接「∃ a. Single a_b => できるか」となるが
        -- mathlib の補題 `Relation.TransGen.mono` を用いても可
        -- ここでは超直接に "x, y" 到達はこう" とは示しづらいので
        -- もう少し一工夫: 要素全体集合 α は R'R に閉じている(すぐに示せる) ので x ∈ α => y ∈ α trivially ではなく
        --   => これだけだと trivial なので最終的には contradiction で済む
        -- ここでは一番簡単に contradiction へ：

        by_contra not_xy
            -- 背理法の仮定を打ち消す「R'R x y」を構築しよう。
            -- ここで "∀ s ∈ S(R'R), x ∈ s ⇒ y ∈ s" はまさに "R_hat(S(R'R)) x y"
        let h_hat : ∀ s ∈ S (R' R), x ∈ s → y ∈ s := this
        -- すると x,y ∈ R_hat(S(R'R)) => R'R x y が言えるかどうか… もう一度同じ背理法を使う？ 再帰ループ注意
        -- 代わりに、簡単な特定集合を考える: T = { z | R'R x z }. T は R'R-閉 で x ∈ T. cand=∅ ⇒ y ∈ T => R'R x y.
        let T :Finset α:= { z | Relation.ReflTransGen R x z }
        -- T が R'R に閉じていることを示す

        suffices T ∈ S (R' R) ∧ x ∈ T by
          --obtain ⟨h1,h2⟩ := h
          have : y ∈ T := by
            by_contra hynT
            have T_family : T ∈ Family := by
              simp_all only [Finset.powerset_univ, Finset.not_mem_empty, IsEmpty.forall_iff, implies_true, and_true,
                exists_const, not_false_eq_true, Finset.mem_filter, Finset.mem_univ, true_and, and_self,
                not_true_eq_false, cand, allSubs, Family, T]
            -- cand=∅ なのに T ∈ Family => cand≠∅ 矛盾
            simp_all only [Finset.powerset_univ, Finset.not_mem_empty, IsEmpty.forall_iff, implies_true, and_true,
              exists_const, not_false_eq_true, Finset.mem_filter, Finset.mem_univ, true_and, and_self,
              not_true_eq_false, cand, allSubs, Family, T]
          -- よって y ∈ T => R'R x y
          rename_i this_2
          --simp_all only [Finset.powerset_univ, Finset.not_mem_empty, IsEmpty.forall_iff, implies_true, and_true,
          --  exists_const, not_false_eq_true, Finset.mem_filter, Finset.mem_univ, true_and, and_self, cand, allSubs,
          --  Family, T]
          obtain ⟨left, right⟩ := this_2
          let ht := h_hat T left right
          --これでは矛盾にならない。not_xyと矛盾するのか？candのemptyとは矛盾しないというか、y in Tの場合は、candの要素にならない。
          have : R' R x y:=
          by
            dsimp [R']
            dsimp [S] at left
            rw [Finset.mem_filter] at left
            dsimp [R'] at left
            dsimp [T] at left
            simp at left
            simp_all only [Finset.powerset_univ, Finset.not_mem_empty, IsEmpty.forall_iff, implies_true, and_true,
              exists_const, not_false_eq_true, cand, allSubs, Family, T, ht]
            dsimp [R'] at not_xy
            dsimp [S] at hxy
            dsimp [R_hat] at hxy
            simp at hxy
            sorry

        constructor
        . -- T ∈ S(R'R)
          simp_all only [Finset.powerset_univ, Finset.not_mem_empty, IsEmpty.forall_iff, implies_true, and_true,
            exists_const, not_false_eq_true, cand, allSubs, Family, T]
          apply Finset.mem_filter.mpr
          simp_all only [Finset.mem_univ, Finset.mem_filter, true_and]
          intro x_1 y_1 a a_1
          apply a_1.trans a
          -- hab : R'R a b, ha : a ∈ T => R'R x a
          -- => R'R x b => b ∈ T
        . -- x ∈ T
          simp_all only [Finset.powerset_univ, Finset.not_mem_empty, IsEmpty.forall_iff, implies_true, and_true,
            exists_const, not_false_eq_true, Finset.mem_filter, Finset.mem_univ, true_and, cand, allSubs, Family, T]
          apply Relation.ReflTransGen.refl

      case neg =>
        sorry --maxを求める関数は別に書く。
        /-
        let sMax := cand.max' ⟨_, Finset.nonempty_of_ne_empty cEmpty⟩
        have sMax_in : sMax ∈ cand := Finset.maxBy_mem neg
        use (sMax : Set α)
        constructor
        . exact sMax_in
        . intro t t_in sub_st
          let cmp := compare sMax.card t.card
          match cmp with
          | Ordering.lt => contradiction
          | Ordering.eq =>
            apply Finset.coe_inj.1
            apply Finset.eq_of_subset_of_card_eq sub_st
            rw [←cmp]
          | Ordering.gt => rfl
        -/


    -- 上で得られた「包含関係で極大」な要素 s を取り出す
    obtain ⟨s,  sMaximal⟩ := existsMaxFamily
    obtain ⟨s_inSR', sMaximal⟩ := sMaximal

    /-
      s ∈ S(R'R) : ∀ a b, R' R a b → (a ∈ s → b ∈ s)
      x ∈ s, y ∉ s
      さらに s は Family の中で極大 (包含関係で)

      ここで "R'R" が "R" の推移的閉包なので R a b ⇒ R'R a b。
      よって s ∈ S(R'R) ⇒ s は R に対しても閉じている。
      => s ∈ S(R)
    -/
    have s_in_S_R : (s : Finset α) ∈ (S R) := by
      dsimp [S]
      dsimp [Family] at sMaximal
      rw [Finset.mem_filter]
      constructor
      simp_all only [Finset.mem_filter, Finset.mem_univ, true_and, and_imp, Family]

      simp at sMaximal

      intro a b rab ha --元々のxとyとこのx' y'の関係がわからない。
      dsimp [Family] at s_inSR'
      rw [Finset.mem_filter] at s_inSR'

      let si := s_inSR'.2.1
      dsimp [S] at si
      dsimp [R']  at si
      rw [Finset.mem_filter] at si
      let si2 := si.2

      --#check sMaximal s s_inSR'.2.1 --この式は意味がない。sの極大性を言っている条件なので、sを入れても意味がない。
      sorry --Familyの極大性から、R x yを言いたいみたいだけど、よくわからず。
      --exact sMaximal (Relation.ReflTransGen.single rab) ha

      /-
      intro a b rab ha
      -- R a b => R'R a b (1ステップ)
      exact s_inSR' (Relation.TransGen.single rab) ha
      -/

    /-
      ここで「R_hat(S(R)) x y」より「∀ s ∈ S(R), x ∈ s → y ∈ s」。
      とくにこの s に適用すると、x ∈ s なら y ∈ s となるが y ∉ s との矛盾。
    -/
    have y_in_s : y ∈ s :=
    by
      apply hxy s s_in_S_R
      simp_all only [Finset.mem_filter, Finset.mem_univ, true_and, and_imp, Family]

    simp_all only [Finset.mem_filter, Finset.mem_univ, not_true_eq_false, and_false, Family]

end FiniteReconstruction
-/
