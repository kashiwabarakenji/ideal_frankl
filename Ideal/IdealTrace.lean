-- vをtraceするオペレーション。traceの操作はIdealDegreeOneで使われている。
--ただ、唯一使われているtrace_hyperedge_equivがメインの照明で使われてないので、結果的にメインの証明に使われてない。
--一般のtraceに対して、numberやtotalを計算するのは、難しい。vの次数が1の場合に限って証明では使われている。
--本当は、{v}がhyperedgeでないケースはもっとtraceを前面に出して議論しても良かった。
--今はdeletion+全体集合という感じで、deletionを利用して計算している。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
--import Mathlib.Init.Data.Nat.Lemmas
--import Mathlib.Data.Bool.Basic
import Mathlib.Tactic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import LeanCopilot

variable {α : Type} [DecidableEq α] [Fintype α]

open Finset

namespace Ideal.IdealTrace  --なぜか名前空間が違う。

def trace {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2): SetFamily α :=
  { ground := F.ground.erase x,
    sets := λ s => (x ∉ s) ∧ (F.sets s ∨ F.sets (s ∪ {x})),
    nonempty_ground := ground_nonempty_after_minor F.ground x hx ground_ge_two,
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

--idealという性質が、traceの演算で閉じていることの証明？
instance trace_ideal_family (F : IdealFamily α) (x : α) (hx : F.sets {x} ) (ground_ge_two: F.ground.card ≥ 2): IdealFamily α :=
{
  trace (F.toSetFamily) x (by { exact F.inc_ground {x} hx (by simp) }) ground_ge_two with

  has_empty := by
    simp_all only [Bool.decide_eq_false, not_false_eq_true, decide_eq_false_iff_not]
    constructor
    intro h
    simp at h
    right
    exact hx,

  has_ground := by
    let thisF := trace (F.toSetFamily) x (by { exact F.inc_ground {x} hx (by simp) }) ground_ge_two
    simp_all only [Bool.decide_eq_false, not_false_eq_true, decide_eq_false_iff_not]
    unfold IdealFamily.toSetFamily
    unfold trace
    unfold SetFamily.sets
    unfold SetFamily.ground
    --x ∉ (trace F.toSetFamily x ⋯ ground_ge_two).ground
    have sg: thisF.sets (F.ground.erase x) := by
      constructor
      intro h
      simp at h
      right
      rw [erase_insert F.ground x (by { exact F.inc_ground {x} hx (by simp) }) ]
      exact F.has_ground
    have sgg: thisF.sets thisF.ground := by
      apply sg
    exact sgg,

  down_closed := by
    let thisF := trace (F.toSetFamily) x (by { exact F.inc_ground {x} hx (by simp) }) ground_ge_two
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
        --goal (trace F.toSetFamily x ⋯ ground_ge_two).sets A
        simp at h --h : B ∪ {x} = F.ground

        have fgx: F.ground ∪ {x} = F.ground := by
          simp_all [hxG]
        have bxf: B ∪ {x} = F.ground := by
          simp [h, fgx]
        have bfg: B = F.ground.erase x:= by
          simp [← bxf]
          exact (union_erase_singleton B x nxB).symm
        contradiction
}

end Ideal.IdealTrace
