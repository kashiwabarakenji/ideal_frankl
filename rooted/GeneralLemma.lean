import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import LeanCopilot

--open Finset

variable {α : Type} [DecidableEq α] [Fintype α]

omit [Fintype α]
lemma exists_one_elements_removed {A B : Finset α} (hBA : B ⊆ A) (hcard : B.card = A.card - 1) (geq1 :A.card ≥ 1):
  ∃ x :α , x ∈ A ∧ A \ {x} = B :=
by
  have h : (A \ B).card = 1 :=
  by
    rw [Finset.card_sdiff hBA, hcard]
    exact Nat.sub_sub_self geq1

  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h

  use x
  constructor
  · have : x ∈ A := (Finset.mem_sdiff.mp (hx.symm ▸ Finset.mem_singleton_self x)).1
    exact this
  · rw [←hx]
    simp
    exact hBA

lemma exists_two_elements_removed {A B : Finset α} (hBA : B ⊆ A) (hcard : B.card = A.card - 2) (geq2 :A.card ≥ 2):
  ∃ x y :α , x ∈ A ∧ y ∈ A ∧ A \ {x, y} = B :=
by
  -- `A \ B` の要素数が 2 であることを確認
  have h : (A \ B).card = 2 := by
    rw [Finset.card_sdiff hBA, hcard]
    exact Nat.sub_sub_self geq2

  obtain ⟨x, y, hx⟩ := Finset.card_eq_two.mp h

  use x, y
  have : {x,y}⊆ A :=
  by
    simp_all only [ge_iff_le, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
      Finset.card_singleton, Nat.reduceAdd, ne_eq]
    obtain ⟨left, right⟩ := hx
    simp [← right]
  constructor
  · -- x ∈ A
    have : x ∈ A :=
    by
       simp_all only [ge_iff_le, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
         Finset.card_singleton, Nat.reduceAdd, ne_eq]
       obtain ⟨left, right⟩ := hx
       apply this
       simp_all only [Finset.mem_insert, Finset.mem_singleton, or_false]
    exact this
  · constructor
    · have : y ∈ A :=
      by
        simp_all only [ge_iff_le, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
          Finset.card_singleton, Nat.reduceAdd, ne_eq]
        obtain ⟨left, right⟩ := hx
        apply this
        simp_all only [Finset.mem_insert, Finset.mem_singleton, or_true]
      exact this
    ·
      simp_all only [ge_iff_le, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
        Finset.card_singleton, Nat.reduceAdd, ne_eq]
      obtain ⟨left, right⟩ := hx
      rw [propext (sdiff_eq_comm hBA this)] at right
      exact right

--subtypeに関する補題。
lemma subtype_val_eq {α : Type} {p : α → Prop} (x y : Subtype p) :
    x = y ↔ Subtype.val x = Subtype.val y := by
  apply Iff.intro
  · intro h; rw [h]
  · intro h; ext; exact h

omit [Fintype α] in
lemma ssubset_lem (s t : Finset α) (v : α) (h1 : s ⊂ t) (h2 : t ⊆ s ∪ {v}) : t = s ∪ {v} :=
by
  -- 真部分集合の定義より、s ⊆ t かつ s ≠ t
  have h3 : s ⊆ t := by
    rw [Finset.ssubset_def] at h1
    simp_all only
  have h4 : s ≠ t := by
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only [Finset.subset_union_left, subset_refl]
    rw [Finset.ssubset_def] at h1
    simp_all only [subset_refl, not_true_eq_false, and_false]

  -- v が t に含まれていることを示す
  have hv_in_t : v ∈ t :=
    by
      by_contra hv_not_in_t
      -- 仮定より t ⊆ s ∪ {v}
      -- v ∉ t より t ⊆ s が成り立つ
      have h_t_subset_s : t ⊆ s := by
        rw [Finset.union_comm] at h2
        rw [Finset.subset_iff]
        rw [Finset.subset_iff] at h2
        intro x hx
        simp_all only [Finset.mem_union, Finset.mem_singleton, ne_eq]
        obtain h | h := h2 hx
        · subst h
          simp_all only
        · simp_all only
      exact h4 (Finset.Subset.antisymm h3 h_t_subset_s)

  -- s ∪ {v} ⊆ t を示す
  have h_s_union_v_subset_t : s ∪ {v} ⊆ t :=
    by
      intros x hx
      cases Finset.mem_union.1 hx with
      | inl hs => exact h3 hs
      | inr hv =>
        have : v ∈ t := hv_in_t
        simp_all only [ne_eq, Finset.mem_union, or_true, Finset.mem_singleton]

  -- s ∪ {v} = t を示す
  exact Finset.Subset.antisymm h2 h_s_union_v_subset_t
/-
--Mathlibにないと思って証明したが、Finset.nonempty_iff_ne_emptyを使ってNonemptyを使えば良いとClaudeに教えてもらった。
lemma Finset.exists_mem_of_ne_empty2 {α : Type} [DecidableEq α] (s : Finset α) (h : s ≠ ∅) :
  ∃ x, x ∈ s :=
by
  -- Finset の内部構造を展開
  match s with
  | ⟨val, nodup⟩ =>
  simp at h -- s ≠ ∅ を Multiset の条件に変換
  -- Multiset に要素があることを証明
  simp_all only [Finset.mem_mk]
  contrapose! h
  ext a : 1
  simp_all only [Finset.mem_mk, Finset.not_mem_empty]
-/
--結果的には、これで良かった。Nonemptyというのは、要素が存在するのと同じだった。
