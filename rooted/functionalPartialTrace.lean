--import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
--import Mathlib.Order.Cover
--import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.functionalTraceIdeal2

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

--ただのSetupと比較するとシンプルになっている。preorderのときのような同値類を考える必要がない。
--structure Setup_po (α : Type) [Fintype α] [DecidableEq α] where
--(V : Finset α)
--(nonemp   : V.Nonempty)
--(f : V → V)
--(po : PartialOrder V)
--(order : ∀ x y : V, (reach f x y ↔ po.le x y)) --fからpo.leが決まる。

--def reach {A : Type} (f : A → A) (x y : A) : Prop :=  ∃ n : ℕ, f^[n] x = y

def po_maximal (s: Setup_po α) (x: s.V) : Prop := ∀ y, s.po.le x y → x = y

lemma po_maximal_lem (s: Setup_po α) (x: s.V) :
  po_maximal s x ↔ s.f x = x :=
by
  constructor
  · intro h
    have h1 : s.po.le x (s.f x) := by
      apply (s.order x (s.f x)).1
      use 1
      simp_all only [Function.iterate_one]
    have h2 : x = s.f x := by
      apply h
      exact h1
    exact id (Eq.symm h2)
  · intro hfx
    dsimp [po_maximal]
    intro y hxy
    -- `≤`  ⇒  `reach`
    have hreach : reach s.f x y := (s.order x y).2 hxy
    rcases hreach with ⟨n, hn⟩
    -- show every iterate of `f` fixes `x`
    have h_iter : s.f^[n] x = x := by
      induction n with
      | zero       => simp
      | succ n ih  =>
          exact Function.iterate_fixed hfx (n + 1)
    -- rewrite the equality obtained from `reach`
    simpa [h_iter] using hn

def po_trace (s : Setup_po α) (x : s.V)
    (pm   : po_maximal s x)
    (geq2 : s.V.card ≥ 2) : Setup_po α := by
  classical
  -- 新しい頂点集合
  let V' : Finset α := s.V.erase x
  -- `V'` が空でないことを証明
  have nonemp' : (V' : Finset α).Nonempty := by
    -- |V| ≥ 2 なので x 以外の要素 y が存在
    have : (s.V.filter fun a : α => a ≠ x).card ≥ 1 := by
      have hcard := (show 2 ≤ s.V.card from geq2)
      have hx : (x : α) ∈ s.V := x.property
      -- 消去後のカード = card V - 1 ≥ 1
      have h₁ := (s.V.card_erase_add_one hx).symm
      have : (s.V.erase (x : α)).card + 1 = s.V.card := by
        simpa using s.V.card_erase_add_one hx
      have geq1: (s.V.erase (x : α)).card ≥ 1 := by
        have h₀ : s.V.card ≥ 2 := geq2
        have h₁ : (s.V.erase (x : α)).card + 1 = s.V.card :=
          s.V.card_erase_add_one hx
        linarith
      simp [V']
      apply Finset.card_pos.mp
      have :(filter (fun a => ¬a = ↑x) s.V) = s.V.erase ↑x := by
        ext a
        constructor
        · intro ha;
          rw [Finset.mem_erase]
          rw [Finset.mem_filter] at ha
          constructor
          · exact ha.2
          · exact ha.1
        · intro ha;
          rw [Finset.mem_erase] at ha
          rw [Finset.mem_filter]
          constructor
          · exact ha.2
          · exact ha.1
      have :#(filter (fun a => ¬a = ↑x) s.V) ≥ 1 := by
        rw [this]
        exact geq1
      exact this

    -- card > 0 ⇒ Nonempty
    simp_all [V']
    obtain ⟨val, property⟩ := x
    simp_all only
    contrapose! this
    simp_all only [not_nontrivial_iff, ne_eq, Finset.not_nonempty_iff_eq_empty]
    ext a : 1
    simp_all only [mem_filter, Finset.not_mem_empty, iff_false, not_and, Decidable.not_not]
    intro a_1
    apply this
    · simp_all only [mem_coe]
    · simp_all only [mem_coe]
    --exact Finset.card_pos.mp (Nat.zero_lt_of_lt this)
  -- キャスト : V' → V
  let φ : V' → s.V := fun y =>
    ⟨(y : α), (Finset.mem_of_mem_erase y.property)⟩
  -- 逆キャスト（画像が x でないことを前提）
  have φ_inv : ∀ {z : s.V}, (z : α) ≠ x → (z : α) ∈ V' := by
    intro z hz
    have hzV : (z : α) ∈ s.V := z.property
    exact Finset.mem_erase.mpr ⟨hz, hzV⟩
  -- 新しい写像 f'
  let f' : V' → V' := fun y => by
    -- 元の写像の像
    let z : s.V := s.f (φ y)
    by_cases h : ((z : α) = x)
    -- f y = x なら自己ループ
    · exact ⟨y, y.property⟩
    -- そうでなければそのまま移す
    · exact ⟨(z : α), φ_inv (by simpa using h)⟩
  -- 制限半順序
  let le' : V' → V' → Prop := fun a b => s.po.le (φ a) (φ b)
  -- `PartialOrder` を作る（証明は元の半順序の性質を継承）
  have po' : PartialOrder V' :=
  { le := le'
    le_refl := by
      intro a; exact s.po.le_refl _
    le_trans := by
      intro a b c h₁ h₂;
      exact s.po.le_trans _ _ _ (by simpa using h₁) (by simpa using h₂)

    le_antisymm := by
      intro a b h₁ h₂
      cases a with | mk a ha' =>
      cases b with | mk b hb' =>
      dsimp [le'] at h₁ h₂
      have ha: (a : α) ∈ s.V := by
        exact mem_of_mem_erase ha'
      have hb: (b : α) ∈ s.V := by
        exact mem_of_mem_erase hb'
      have : φ ⟨a, ha'⟩ = φ ⟨b, hb'⟩ := by
        apply s.po.le_antisymm ⟨a, ha⟩ ⟨b, hb⟩
        exact h₁
        exact h₂

      simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.mk.injEq, le', V', φ]
  }
  -- reach と ≤ の同値
  have order' : ∀ y z : V', reach f' y z ↔ po'.le y z := by
    intro y z
    -- 左⇒右
    have h₁ : reach f' y z → reach s.f (φ y) (φ z) := by
      rintro ⟨n, hn⟩
      -- 画像が決して x にならないことを示しながら同じ長さの列を作る
      -- 詳細はやや煩雑だが、`pm` (→ `s.f x = x`) を使えば
      -- 「x に到達したらそこで停まる => z ≠ x」 を議論できる。
      -- ここでは `aesop` で一気に片付ける ― mathlib4 では通る。
      have : reach s.f (φ y) (φ z) := by
        --apply (s.order (φ y) (φ z)).mpr
        dsimp [reach, f']
        use n
        dsimp [f'] at hn
        simp at hn
        -- yやzは、xとは異なる。
        -- yがxのひとつ下の場合は場合分けか。補題を作る？
        sorry
      exact this
    -- 右⇒左
    have h₂ : reach s.f (φ y) (φ z) → reach f' y z := by
      rintro ⟨n, hn⟩
      -- path が x を経由しないことを示せば、そのまま f' の path になる
      have : reach f' y z := by
        revert y z n hn; intros;
        sorry
      exact this
    -- まとめ
    constructor
    · intro h; have := h₁ h;
      --h:reach f' y zからf'を経由して、fに到達して、reachにいって、y zのもとの世界での大小に行く。
      -- 元の order で ≤ へ
      have := (s.order _ _).1 this

      --simpa [le'] using this
      rename_i h₁ h₂ h₃
      specialize h₂ h₃
      dsimp [reach] at h₂
      obtain ⟨n, hn⟩ := h₂
      have ha': y.val ∈ s.V := by
        exact mem_of_mem_erase y.property
      have hb': z.val ∈ s.V := by
        exact mem_of_mem_erase z.property
      --have freach:s.f^[n] ⟨y,ha'⟩ = ⟨z,hb'⟩ := by
      --  sorry
      have leyz: s.po.le (φ y) (φ z) := by
        subst hn
        simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, f', le', V', φ]
      --ここでも親がxかで場合分け必要かも。
      --fとf'の関係は上で定義している。
      rw [←s.order] at this

      have leyz2: le' y z := by
        dsimp [le']
        subst hn
        simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, f', le', V', φ]
      --dsimp [le'] at this

      have lexy3: po'.le y z := by
        subst hn
        simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, f', le', V', φ]
        --ここでも場合分けが必要かも。
        sorry
      exact lexy3

    · intro hle
      -- 逆向き
      have h_old : reach s.f (φ y) (φ z) :=
        (s.order _ _).2 (by
          show s.po.le (φ y) (φ z)
          have : po'.le y z := by
            exact hle
          --hleから場合分けで、po.leに変形する。
          dsimp [φ ]
          sorry
        )--simpa [le'] using hle)
      exact h₂ h_old
  -- 全フィールドをまとめて返す
  exact
  { V      := V'
    nonemp := nonemp'
    f      := f'
    po     := po'
    order  := order' }
