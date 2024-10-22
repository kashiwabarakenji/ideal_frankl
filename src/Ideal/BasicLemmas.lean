import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic
import Ideal.BasicDefinitions
import LeanCopilot

open Finset

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

-- 空集合と全体集合が異なることの証明
omit [DecidableEq α] in
theorem empty_ne_univ : (∅ : Finset α) ≠ Finset.univ :=
  by
    -- 証明を進めるために必要な簡約
    simp_all only [ne_eq]
    -- 矛盾を導く
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp [Finset.eq_univ_iff_forall] at a


--3つ同じ定理がある。
--下と同じ定理。こちらを使う。
omit [Fintype α] [Nonempty α] in
theorem erase_union_singleton (H : Finset α) (h1 : d = H.erase v) (h2 : v ∈ H) : H = d ∪ {v} :=
by
  -- 仮定 h1 を使って hd3 を書き換える
  rw [h1]
  -- 証明するべきは (hd3.erase v) ∪ {v} = hd3 であること
  apply Finset.ext
  intro x
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase]
  -- x が v であるかどうかで場合分けする
  by_cases h : x = v
  -- x = v の場合
  · rw [h]
    simp [h2]
      -- x ≠ v の場合
  · simp [h]

omit [Fintype α] [Nonempty α]
lemma erase_insert_eq (H G : Finset α) (x : α) : x ∈ H → Finset.erase H x = G → H = G ∪ {x} :=
  by
    intro a a_1
    exact erase_union_singleton H a_1.symm a

--上と同じ定理。非推奨。上と同じなので消して良い。
/-lemma erase_insert_eq' (H G : Finset α) (x : α) : x ∈ H → Finset.erase H x = G → H = G ∪ {x} :=
  by
    --rename_i inst inst_1 inst_2
    intro a a_1
    subst a_1
    ext1 a_1
    simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, Finset.mem_singleton]
    apply Iff.intro
    · intro a_2
      simp_all only [and_true]
      tauto
    · intro a_2
      cases a_2 with
      | inl h => simp_all only
      | inr h_1 =>
        subst h_1
        simp_all only
-/

lemma erase_insert (H : Finset α) (x : α) : x ∈ H → (H.erase x) ∪ {x} = H :=
  by
    intro a
    let d := H.erase x
    have h1 : d = H.erase x := rfl
    rw [←h1]
    exact (erase_union_singleton H h1 a).symm

--シングルトンを消してから足すと元の集合に戻る。非推奨。上と同じなので消して良い。
/- lemma erase_insert': ∀ (s : Finset α) (x : α), x ∈ s → (s.erase x) ∪ {x} = s := by
  intro s x hx
  ext y
  constructor
  intro hy
  simp_all only [mem_union, mem_erase, mem_singleton]
  by_cases h: y = x
  on_goal 1 => simp [*]
  tauto
  simp only [mem_erase, mem_union]
  contrapose!
  --rename_i inst _ _
  intro a
  simp_all only [ne_eq, mem_singleton, not_false_eq_true]
-/



--シングルトンを足してから消すと元の集合に戻る。
theorem union_erase_singleton (d : Finset α) (v : α) (dd : v ∉ d) : (d ∪ {v}).erase v = d :=
by
  ext x
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
  constructor
  -- `x ∈ (d ∪ {v})` かつ `x ≠ v` ならば `x ∈ d`
  intro h
  cases h.2 with
  | inl hx => exact hx
  | inr hx =>
     rw [hx] at h
     obtain ⟨hx, _⟩ := h
     contradiction
  -- `x ∈ d` ならば `x ∈ (d ∪ {v}).erase v`
  · intro hx
    constructor
    --  x ≠ v
    intro hh
    rw [hh] at hx
    contradiction
    --  x ∈ d ∨ x = v
    exact Or.inl hx

--lemmaのところに移動してもよい。
theorem erase_inj_of_mem {s t : Finset α} {x : α} (hx : x ∈ s) (ht : x ∈ t) :
  Finset.erase s x = Finset.erase t x ↔ s = t :=
by
  constructor
  -- まず、Finset.erase s x = Finset.erase t x から s = t を導きます。
  · intro h
    apply Finset.ext
    intro a
    by_cases ha : a = x
    -- a が x に等しい場合
    · rw [ha]
      simp_all

    -- a が x に等しくない場合
    simp only [ha, eq_self_iff_true] at h
    · constructor
      intro h1 -- a ∈ s
      have hh: a ∈ s.erase x := Finset.mem_erase_of_ne_of_mem ha h1
      rw [h] at hh
      exact Finset.mem_of_mem_erase hh
      intro h2 -- a ∈ t
      have hh: a ∈ t.erase x := Finset.mem_erase_of_ne_of_mem ha h2
      rw [←h] at hh
      exact Finset.mem_of_mem_erase hh

  -- 次に、s = t から Finset.erase s x = Finset.erase t x を導きます。
  · intro h
    rw [h]

-- フィンセットの消去が等しいことから元のセットが等しいことを証明する補助定理。上のerase_inj_of_memと同じ。
--これの包含関係版も作りたい。
/-
lemma set_eq_of_erase_eq {A : Finset α} {B : Finset α} {x : α} (hxA : x ∈ A) (hxB : x ∈ B) (h : Finset.erase A x = Finset.erase B x) : A = B :=
  by
    apply Finset.ext
    intro y
    constructor
    · intro hy
      by_cases hxy : y = x
      · rw [hxy]
        exact hxB
      · have h1 : y ∈ Finset.erase A x := Finset.mem_erase_of_ne_of_mem hxy hy
        rw [h] at h1
        exact Finset.mem_of_mem_erase h1
    · intro hy
      by_cases hxy : y = x
      · rw [hxy]
        exact hxA
      · have h1 : y ∈ Finset.erase B x := Finset.mem_erase_of_ne_of_mem hxy hy
        rw [←h] at h1
        exact Finset.mem_of_mem_erase h1
-/
/-
--上と同じ補題。使ってないので消して良い。
lemma erase_eq_iff_of_mem {s₁:Finset α}{s₂:Finset α}(hx1: x ∈ s₁)(hx2: x ∈ s₂): s₁.erase x = s₂.erase x → s₁ = s₂:= by
  intro h
  apply Finset.ext
  intro y
  by_cases hy : y = x
  · rw [hy]
    exact ⟨λ _ => hx2, λ _ => hx1⟩
  · have h1 : y ∈ s₁ ↔ y ∈ s₁.erase x := by
      constructor
      · intro hy1
        exact Finset.mem_erase.mpr ⟨hy, hy1⟩
      · intro hy1
        exact Finset.mem_of_mem_erase hy1
    have h2 : y ∈ s₂ ↔ y ∈ s₂.erase x := by
      constructor
      · intro hy2
        exact Finset.mem_erase.mpr ⟨hy, hy2⟩
      · intro hy2
        exact Finset.mem_of_mem_erase hy2
    --h1 : y ∈ s₁ ↔ y ∈ s₁.erase x
    rw [h1, h2, h]
    -/

lemma subset_of_erase_subset {A B : Finset α}  {x : α} (hxA : x ∈ A) (hxB : x ∈ B) (h : A.erase x ⊆ B.erase x) : A ⊆ B :=
by
  -- A = A.erase x ∪ {x} を利用する
  rw [←Finset.insert_erase hxA]
  -- B = B.erase x ∪ {x} を利用する
  rw [←Finset.insert_erase hxB]
  -- A.erase x ⊆ B.erase x と hxB を使って A ⊆ B を証明する
  --goal insert x (A.erase x) ⊆ insert x (B.erase x)
  apply Finset.insert_subset_insert x h


--足したものにさらに足してもかわらない.
lemma insert_union_eq (G : Finset α) (x : α) : insert x (G ∪ {x}) = G ∪ {x} :=
  by
    simp_all only [Finset.mem_union, Finset.mem_singleton, or_true, Finset.insert_eq_of_mem]

-- 属さない要素を足したら、真に大きくなる。
lemma ssubset_insert (G : Finset α) (x : α) : x ∉ G → G ⊂ G ∪ {x} :=
  by

    intro hxG  -- x ∉ G であることを仮定
    -- 部分集合であることを示す
    have subset : G ⊆ G ∪ {x} := by
      intro y hy
      simp_all only [Finset.mem_union, Finset.mem_singleton, true_or]
    -- 真部分集合であることを示す
    have neq : G ≠ G ∪ {x} :=
      by
        intro eq
        -- x ∉ G であるが、x ∈ G ∪ {x} であるため矛盾が生じる
        have x_in_union := Finset.mem_insert_self x G
        rw [eq] at x_in_union
        rw [insert_union_eq] at x_in_union
        rw [eq] at hxG
        contradiction
    -- 部分集合かつ等しくないので真部分集合であることを結論づける
    exact Finset.ssubset_iff_subset_ne.mpr ⟨subset, neq⟩

--非空と、要素数が1以上であることの同値性
omit [DecidableEq α] in
lemma card_ne_zero_iff_nonempty (s : Finset α) : s.card ≠ 0 ↔ s ≠ ∅ :=
  by
    constructor
    · intro h
      contrapose! h
      exact Finset.card_eq_zero.mpr h
    · intro h
      contrapose! h
      exact Finset.card_eq_zero.mp h

lemma card_union_singleton_sub_one {G : Finset α} {x : α} : x ∉ G → x ∈ G ∪ {x} → G.card = (G ∪ {x}).card - 1 :=
  by
    intro xnG -- x ∉ G
    intro _ -- x ∈ G ∪ {x} ゴールはG.card = (G ∪ {x}).card - 1
        -- Use the theorem `Finset.card_erase_of_mem`
        --{α : Type u_1}  {s : Finset α}  {a : α}  [DecidableEq α]
        -- a ∈ s → (s.erase a).card = s.card - 1
    let G' := G ∪ {x}
    have GdG: G' = G ∪ {x} := by rfl
    have gg: G'.erase x = G := by exact union_erase_singleton G x xnG
    have gxH : x ∈ G' := by exact Finset.mem_union_right G (Finset.mem_singleton_self x)
    have ggg: G.card = (G ∪ {x}).card - 1 :=
      by
        have h_erase := union_erase_singleton G x xnG
        rw [←h_erase]
        rw [gg]
        rw [←GdG]
        rw [←h_erase]
        rw [←GdG]
        exact Finset.card_erase_of_mem gxH
    exact ggg

omit [DecidableEq α] in
theorem ne_implies_not_mem_singleton (x y: α)(h : y ≠ x) : y ∉ ({x} : Finset α) :=
  by
    intro h1
    rw [mem_singleton] at h1
    contradiction

omit [DecidableEq α] in
theorem not_mem_singleton_implies_ne (h : y ∉ ({x} : Finset α)) : y ≠ x :=
  by
    intro heq
    rw [heq] at h
    simp at h

omit [DecidableEq α] in
theorem my_card_le_of_subset {s t:Finset α} (h : s ⊆ t) : s.card ≤ t.card :=
  Finset.card_le_card h

theorem diff_diff_eq_diff_diff (A B C : Finset α) : (A \ B) \ C = (A \ C) \ B :=
  by
    ext x
    simp only [mem_sdiff, mem_union, mem_inter, not_and, not_or, not_not]
    constructor
    -- (x ∈ (A \ B) \ C → x ∈ (A \ C) \ B)
    · intro h
      constructor
      -- x ∈ A \ C
      · constructor
        exact h.1.1
        exact h.2
      -- x ∉ B
      exact h.1.2
      -- (x ∈ (A \ C) \ B → x ∈ (A \ B) \ C)
    · intro h
      constructor
      -- x ∈ A \ B
      · constructor
        exact h.1.1
        exact h.2
      -- x ∉ C
      exact h.1.2

-- 命題: 空集合の部分集合は空集合である
lemma subset_empty_eq_empty {α : Type} [DecidableEq α] {s : Finset α} (h : s ⊆ (∅ : Finset α)) : s = ∅ :=
by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intros x hx
  have : x ∈ ∅ := h hx
  exact Finset.not_mem_empty x this

lemma mem_of_mem_list {α : Type} [DecidableEq α] {a : α} {l : List α} :
  a ∈ l → a ∈ l.toFinset :=
by
  intros h
  rw [List.mem_toFinset]
  exact h

---------------------------
-- ここから集合族っぽい定理集--

--　最大要素の存在
omit [DecidableEq α] in
lemma exists_max_card (S : Finset (Finset α))(h : S ≠ ∅):
  ∃ T ∈ S, T.card = S.sup (λ s => s.card) :=
  by
    -- 空でないことを証明
    rw [←card_ne_zero_iff_nonempty] at h
    rw [Finset.card_ne_zero] at h
    -- 最大の要素が存在することを示す
    have hh := Finset.exists_mem_eq_sup S h (λ s => s.card)
    match hh with
    | ⟨T, hT⟩ =>
      use T
      constructor
      exact hT.left
      exact hT.right.symm

-- 大きさが2以上の場合は、1減らしても1以上の大きさを持つ。
lemma ground_nonempty_after_minor {α : Type} [DecidableEq α] (ground : Finset α) (x : α) (hx: x ∈ ground) (gcard: ground.card ≥ 2) : (ground.erase x).Nonempty :=
  by
    rw [Finset.erase_eq]
    apply Finset.nonempty_of_ne_empty
    by_contra h_empty
    by_cases hA : ground = ∅
    rw [hA] at gcard
    contradiction
    -- ground.card = 1のケース
    have g_eq_x: ground = {x} := by
      ext y
      constructor
      intro hy
      have hy' : y ∈ ground \ {x} := by
          rw [h_empty]
          simp_all only [ge_iff_le, sdiff_eq_empty_iff_subset, subset_singleton_iff, false_or, singleton_ne_empty,
            not_false_eq_true, mem_singleton, not_mem_empty, card_singleton, Nat.not_ofNat_le_one]
      rw [h_empty] at hy'
      contradiction
      -- y ∈ {x}のときに、groundに属することを示す
      intro hy
      have x_eq_y : x = y := by
        rw [mem_singleton] at hy
        rw [hy]
      rw [x_eq_y] at hx
      exact hx
    rw [g_eq_x] at gcard
    rw [Finset.card_singleton] at gcard
    contradiction

/-
-- IntersectionClosedにあった補題
--BasicLemmasに似たようなものがある。使っているが、置き換えれば消せる。
lemma h_erase {G : Finset α} {x : α} :x ∉ G → (G ∪ {x}).erase x = G :=
  by
    intro h -- x ∉ G
    ext y
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
    constructor -- 左辺から右辺と右辺から左辺にわける。y ∈ G ∨ y = xからy ∈ G をしめす。
    ·intro h' -- 左辺から右辺。
     have x_ne_y : x ≠ y := by
       intro hH
       rw [hH] at h
       have hl :=h'.left.symm
       contradiction --ここまででx neq yが証明できた。
     cases h'.right with
     |inl yG =>
      exact yG  -- ここにも到達してなさそう。
     |inr xy =>
      rw [xy] at x_ne_y --ここに到達してなさそう。
      contradiction --ここまででcasesの両側が証明できた?constructionの左辺から右辺も。goalが残っている。

    --右辺から左辺 ゴールは、y ∈ G → y ≠ x ∧ (y ∈ G ∨ y = x)
    intro h' --y ∈ G ゴールは、 y ≠ x ∧ (y ∈ G ∨ y = x)
    constructor
    -- サブゴールは、x neq y
    have x_ne_y2 : x ≠ y := by
      intro hH --x=y
      rw [←hH] at h'  -- x in Gに書き換え。
      contradiction
    exact x_ne_y2.symm
    -- 右側 ゴールは、(y ∈ G ∨ y = x)
    exact Or.inl h'
    --これで、lemmaの証明が完了した。
-/



theorem hyperedges_card_ge_two {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (hground : 1 ≤ F.ground.card) : 2 ≤ number_of_hyperedges F.toSetFamily :=
by
  -- number_of_hyperedges は空集合と全体集合を含むため、少なくとも 2 つのハイパーエッジがあることを示す
  have h_empty : F.sets  ∅ := F.empty_mem
  have h_univ :  F.sets F.ground := F.univ_mem

  -- 空集合と全体集合が distinct（異なる）であることを確認する
  have h_distinct : ∅ ≠ F.ground :=
    by
      intro h_eq
      have : F.ground.card = 0 := by rw [←h_eq, Finset.card_empty]
      linarith [hground]  -- 矛盾を示す

  -- 空集合と全体集合の 2 つの要素が含まれているため、number_of_hyperedges は 2 以上
  simp_all only [one_le_card, ne_eq, ge_iff_le]
  rw [number_of_hyperedges]
  have sublem: {∅, F.ground} ⊆ F.ground.powerset := by
    intro x hx
    simp_all only [mem_insert, mem_singleton, mem_powerset]
    cases hx with
    | inl h =>
      subst h
      simp_all only [empty_subset]
    | inr h_1 =>
      subst h_1
      simp_all only [subset_refl]
  have h1: (({∅} : Finset (Finset α)) ∪ {F.ground}).card ≤ F.ground.powerset.card := by exact my_card_le_of_subset sublem
  have h2: (({∅} : Finset (Finset α)) ∪ {F.ground}).card = 2 := by
    simp_all only [card_powerset, ge_iff_le]
    rw [card_union_of_disjoint]
    · simp_all only [card_singleton, Nat.reduceAdd, le_refl]
    · simp_all only [disjoint_singleton_right, mem_singleton]
      apply Aesop.BuiltinRules.not_intro
      intro a
      simp_all only [Finset.not_nonempty_empty]
  have h3: (({∅} : Finset (Finset α)) ∪ {F.ground}) ⊆ F.ground.powerset.filter F.sets := by
    simp_all only [card_powerset, ge_iff_le]
    intro x hx
    simp_all only [mem_union, mem_singleton, mem_filter, mem_powerset]
    cases hx with
    | inl h =>
      subst h
      simp_all only [empty_subset, and_self]
    | inr h_1 =>
      subst h_1
      simp_all only [subset_refl, and_self]
  simp_all only [card_powerset, ge_iff_le]
  rw [←h2]
  exact Finset.card_le_card h3

-- 定理のステートメント
theorem injective_image_injective {α β : Type} [DecidableEq α] [DecidableEq β]
  (f : α → β) (hf : Function.Injective f) :
  Function.Injective (λ (s : Finset α)=> Finset.image f s) :=
  by
     -- 関数が可逆であることを示すため、任意の集合 s, t に対してs.image f = t.image f ならば s = t であることを示す
    intro s t hs
    -- 集合の等価性を示すために ext を適用し、要素ごとの等価性を確認する
    apply Finset.ext
    intro x
    -- sとtのイメージにおける要素 x の属し方が等しいことを示す
    constructor
    -- まず、x ∈ s ならば x ∈ t を示す
    · intro hx
      -- x ∈ s ならば f x ∈ s.image f
      simp_all only
      have fxs: f x ∈ s.image f := by
        rw [Finset.mem_image]
        use x
      by_contra H
      have fxt: f x ∉ t.image f := by
        rw [Finset.mem_image]
        rw [Function.Injective] at hf
        --simp_all only [Finset.mem_image, not_true_eq_false]
        --obtain ⟨w, h⟩ := fxs
        --obtain ⟨left, right⟩ := h
        by_contra hh
        obtain ⟨w, h⟩ := hh
        obtain ⟨left, right⟩ := h
        have w_eq_x : w = x := hf right
        rw [w_eq_x] at left
        exact H left
      rw [hs] at fxs
      contradiction
    -- 次に、x ∈ t ならば x ∈ s を示す
    · intro hx
      -- x ∈ t ならば f x ∈ t.image f = s.image f だから、sにもxが存在する
      simp_all only
      have fxt: f x ∈ t.image f := by
        rw [Finset.mem_image]
        use x
      by_contra H
      have fxs: f x ∉ s.image f := by
        rw [Finset.mem_image]
        rw [Function.Injective] at hf
        by_contra hh
        obtain ⟨w, h⟩ := hh
        obtain ⟨left, right⟩ := h
        have w_eq_x : w = x := hf right
        rw [w_eq_x] at left
        exact H left
      rw [←hs] at fxt
      contradiction


end Ideal
