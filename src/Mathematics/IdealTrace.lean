import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic
import Mathematics.BasicDefinitions
import Mathematics.BasicLemmas
import LeanCopilot

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

open Finset

namespace Mathematics.IdealTrace

--deletionに限らないかも。名前を変えてBasicLemmasに移動するかも。
lemma ground_nonempty_after_deletion {α : Type} [DecidableEq α] (ground : Finset α) (x : α) (hx: x ∈ ground) (gcard: ground.card ≥ 2) : (ground.erase x).Nonempty :=
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

def trace {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2): SetFamily α :=
  { ground := F.ground.erase x,
    sets := λ s => (x ∉ s) ∧ (F.sets s ∨ F.sets (s ∪ {x})),
    nonempty_ground := ground_nonempty_after_deletion F.ground x hx gcard,
    inc_ground := λ s hs =>
      by
        simp_all only [Bool.decide_and, Bool.decide_eq_true, decide_not, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not]
        obtain ⟨left, right⟩ := hs
        rw [Finset.subset_erase]
        constructor
           -- x ∉ s
        all_goals
          intro h
          exact left h
        -- F.sets s ∨ F.sets (s ∪ {x})
        cases right with
        -- F.sets s
        | inl hh =>
          exact F.inc_ground s hh
        -- F.sets (s ∪ {x})
        | inr hh =>
          have hhh: s ∪ {x} ⊆ F.ground := F.inc_ground (s ∪ {x}) hh
          rename_i _ _ _ _ inst_3
          simp_all only [ge_iff_le]
          intro y hy
          exact hhh (mem_union_left _ hy)
  }



theorem union_erase_singleton2 (d : Finset α) (v : α) (dd:v ∉ d): (d ∪ {v}).erase v = d :=
by
  ext x
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
  constructor
  -- まず、(x ∈ d ∪ {v}) ∧ (x ≠ v) ならば x ∈ d です
  · intro h
    obtain ⟨hx, hne⟩ := h
    by_cases h' : x = v
    -- x = v の場合
    · contradiction
    -- x ≠ v の場合
    · apply Or.elim hne
      -- x ∈ d の場合
      · intro hdx
        exact hdx
      -- x ∈ {v} の場合
      · intro hvs
        rw [hvs] at hne
        contradiction
  -- 次に、x ∈ d ならば x ∈ (d ∪ {v}).erase v です
  · intro h
    -- x ≠ v ∧ (x ∈ d ∨ x = v)
    constructor
    -- x ≠ v
    contrapose! h
    rw [h]
    exact dd
    -- x ∈ d ∨ x = v
    left
    exact h

instance trace_ideal_family (F : IdealFamily α) (x : α) (hx : F.sets {x} ) (gcard: F.ground.card ≥ 2): IdealFamily α :=
{
  trace (F.toSetFamily) x (by { exact F.inc_ground {x} hx (by simp) }) gcard with

  empty_mem := by
    simp_all only [Bool.decide_eq_false, not_false_eq_true, decide_eq_false_iff_not]
    constructor
    intro h
    simp at h
    right
    exact hx,

  univ_mem := by
    let thisF := trace (F.toSetFamily) x (by { exact F.inc_ground {x} hx (by simp) }) gcard
    simp_all only [Bool.decide_eq_false, not_false_eq_true, decide_eq_false_iff_not]
    unfold IdealFamily.toSetFamily
    unfold trace
    unfold SetFamily.sets
    unfold SetFamily.ground
    --x ∉ (trace F.toSetFamily x ⋯ gcard).ground
    have sg: thisF.sets (F.ground.erase x) := by
      constructor
      intro h
      simp at h
      right
      rw [erase_insert F.ground x (by { exact F.inc_ground {x} hx (by simp) }) ]
      exact F.univ_mem
    have sgg: thisF.sets thisF.ground := by
      apply sg
    exact sgg,

  down_closed := by
    let thisF := trace (F.toSetFamily) x (by { exact F.inc_ground {x} hx (by simp) }) gcard
    have hxG: x ∈ F.ground := by
      exact F.inc_ground {x} hx (by simp)
    intro A B hB hB_neq hAB
    simp_all only [Bool.decide_eq_false, not_false_eq_true, decide_eq_false_iff_not]
    obtain ⟨hB_not_x, hB_sets⟩ := hB
    have nxB :x ∉ B := by
       intro h
       contradiction
    have x_not_A: x ∉ A := by
       intro h
       have h_in_B: x ∈ B := by
         exact hAB h
       exact nxB h_in_B

    have hhAB: A ∪ {x} ⊆ B ∪ {x} := by
      intros a ha
      match mem_union.mp ha with
        | Or.inl haA =>
          apply mem_union_left
          exact hAB haA
        | Or.inr hax =>
          apply mem_union_right
          exact hax

    /- なぜかうまくいかない。lambdaの使い方が悪いみたい。
    have hhAB2: A ∪ {x} ⊆ B ∪ {x} :=
      λ a ha =>
        match mem_union.mp ha with
        | Or.inl haA =>
          apply mem_union_left
          exact hAB haA
        | Or.inr hax =>
          apply mem_union_right
          exact hax
    -/

    match hB_sets with
    -- F.sets B
    -- BがF.setsであり、かつxを含まない場合
    |Or.inl hB_sets =>

     have hBnG: B ≠ F.ground := by
        intro h
        rw [h] at nxB
        exact nxB hxG
     have Fsets: F.sets A := by
        exact F.down_closed A B hB_sets hBnG hAB

     have thisFsets: thisF.sets A := by
        dsimp [thisF]
        dsimp [trace]
        constructor
        simp_all
        --exact x_not_A
        exact Or.inl Fsets

     exact thisFsets
    --(down_closed : ∀ (A B : Finset α), sets B → B ≠ ground → A ⊆ B → sets A)

    -- 仮定：F.sets (B ∪ {x})の場合
    -- goal : thisF.sets A　　ただし、x ∉ A
    -- F.sets A ∪ {x} が成り立つことを示す。
    -- よって、thisF.sets A となる。
    |Or.inr hB_sets =>
     --have hBx := F.inc_ground (B ∪ {x}) hB_sets
     --B ∪ {x} = F.groundのIdealFamilyは、冪集合になるので、場合分けした方がいいかも。

     by_cases h: (B ∪ {x}) ≠ F.ground
     case pos =>
        have Fsets: F.sets (A ∪ {x}) := by
          exact F.down_closed (A ∪ {x}) (B ∪ {x}) hB_sets h hhAB
        have thisFsets: thisF.sets A := by
          dsimp [thisF]
          dsimp [trace]
          constructor
          simp_all
          exact Or.inr Fsets
        simp_all only [ne_eq, not_false_eq_true, or_true, thisF]
        --goal x ∈ F.ground ここにもゴールが残っている?
        --exact thisFsets
     --(B ∪ {x}) = F.groundF.sets (A ∪ {x})が成り立たつばあい hに入っている。
     case neg =>
        --goal (trace F.toSetFamily x ⋯ gcard).sets A
        simp at h --h : B ∪ {x} = F.ground
        --成り立つが、使ってない部分をコメントアウト
        --have _: F.sets (B ∪ {x}) := by --使ってない。
        --  rw [h]
        --  exact F.univ_mem
        --have hB_neq2: B ≠ thisF.ground := by
        --  dsimp [thisF]
        --  exact hB_neq
        --have GG: thisF.ground = F.ground.erase x := by
        --  rfl
        --rw [GG] at hB_neq2
        --have BB: B ∪ {x} = (F.ground.erase x)∪{x} := by
        --  rw [erase_insert F.ground x hxG]
        --  simp [h]
        have fgx: F.ground ∪ {x} = F.ground := by
          simp_all [hxG]
        have bxf: B ∪ {x} = F.ground := by
          simp [h, fgx]
        have bfg: B = F.ground.erase x:= by
          simp [← bxf]
          exact (union_erase_singleton B x nxB).symm
        contradiction
}

end Mathematics.IdealTrace
