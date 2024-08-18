import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Tactic
import Mathematics.BasicDefinitions
import LeanCopilot

open Finset

namespace Mathematics

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

-- 空集合と全体集合が異なることの証明
theorem empty_ne_univ : (∅ : Finset α) ≠ Finset.univ :=
  by
    -- 各型クラスのインスタンスを取得
    rename_i _ inst_1 inst_2
    -- 証明を進めるために必要な簡約
    simp_all only [ne_eq]
    -- 矛盾を導く
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp [Finset.eq_univ_iff_forall] at a


--3つ同じ定理がある。
--下と同じ定理。こちらを使う。
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

lemma erase_insert_eq (H G : Finset α) (x : α) : x ∈ H → Finset.erase H x = G → H = G ∪ {x} :=
  by
    intro a a_1
    exact erase_union_singleton H a_1.symm a

lemma erase_insert (H : Finset α) (x : α) : x ∈ H → (H.erase x) ∪ {x} = H :=
  by
    intro a
    let d := H.erase x
    have h1 : d = H.erase x := rfl
    rw [←h1]
    exact (erase_union_singleton H h1 a).symm

--シングルトンを消してから足すと元の集合に戻る。非推奨。上と同じなので消して良い。
lemma erase_insert': ∀ (s : Finset α) (x : α), x ∈ s → (s.erase x) ∪ {x} = s := by
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
  rename_i inst _ _
  intro a
  simp_all only [ne_eq, mem_singleton, not_false_eq_true]

--上と同じ定理。非推奨。上と同じなので消して良い。
lemma erase_insert_eq' (H G : Finset α) (x : α) : x ∈ H → Finset.erase H x = G → H = G ∪ {x} :=
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

-- フィンセットの消去が等しいことから元のセットが等しいことを証明する補助定理
lemma set_eq_of_erase_eq {A B : Finset α} {x : α} (hxA : x ∈ A) (hxB : x ∈ B) (h : Finset.erase A x = Finset.erase B x) : A = B :=
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
lemma card_ne_zero_iff_nonempty (s : Finset α) : s.card ≠ 0 ↔ s ≠ ∅ :=
  by
    constructor
    · intro h
      contrapose! h
      exact Finset.card_eq_zero.mpr h
    · intro h
      contrapose! h
      exact Finset.card_eq_zero.mp h

---------------------------
-- ここから集合族っぽい定理集--

--　最大要素の存在
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

lemma card_union_singleton_sub_one {G : Finset α} {x : α} : x ∉ G → x ∈ G ∪ {x} → G.card = (G ∪ {x}).card - 1 :=
  by
    intro xnG -- x ∉ G
    intro _ -- x ∈ G ∪ {x} ゴールはG.card = (G ∪ {x}).card - 1
        -- Use the theorem `Finset.card_erase_of_mem`
        --{α : Type u_1}  {s : Finset α}  {a : α}  [DecidableEq α]
        -- a ∈ s → (s.erase a).card = s.card - 1
    let G' := G ∪ {x}
    have GdG: G' = G ∪ {x} := by rfl
    have gg: G'.erase x = G := by exact h_erase xnG
    have gxH : x ∈ G' := by exact Finset.mem_union_right G (Finset.mem_singleton_self x)
    have ggg: G.card = (G ∪ {x}).card - 1 :=
      by
        have h_erase := h_erase xnG
        rw [←h_erase]
        rw [gg]
        rw [←GdG]
        rw [←h_erase]
        rw [←GdG]
        exact Finset.card_erase_of_mem gxH
    exact ggg

theorem ne_implies_not_mem_singleton (x y: α)(h : y ≠ x) : y ∉ ({x} : Finset α) :=
  by
    intro h1
    rw [mem_singleton] at h1
    contradiction

theorem not_mem_singleton_implies_ne (h : y ∉ ({x} : Finset α)) : y ≠ x :=
  by
    intro heq
    rw [heq] at h
    simp at h

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

end Mathematics
