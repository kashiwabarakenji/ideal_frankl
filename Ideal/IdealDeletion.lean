import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
--import Mathlib.Init.Function
import Mathlib.Init.Logic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import LeanCopilot

namespace Ideal
variable {α : Type} [DecidableEq α] [Fintype α]

def deletion {α : Type} [DecidableEq α] [Fintype α](F : SetFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2): SetFamily α :=
  { ground := F.ground.erase x,
    sets := λ s => F.sets s ∧ ¬ x ∈ s,
    nonempty_ground := ground_nonempty_after_minor F.ground x hx ground_ge_two

    inc_ground :=

      λ s hs => by
        simp_all only [decide_eq_false_iff_not]
        obtain ⟨left, right⟩ := hs
        have hs' : s ⊆ F.ground := F.inc_ground s left
        exact Finset.subset_erase.2 ⟨hs', right⟩
        }

--infixl:65 " ∖ " => deletion

-- IdealFamilyに対するdeletion操作がIdealFamilyになることの証明。定義の中に証明がある。
def idealdeletion {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2): IdealFamily α :=
{
    ground := F.ground.erase x,

    sets := λ s => (F.sets s ∧ ¬ x ∈ s) ∨ s = F.ground.erase x,

    --(down_closed : ∀ {A B : Finset α}, sets B → B ≠ ground → A ⊆ B → sets A)
    down_closed := λ A B hB hB_ne_ground hAB => by
      unfold SetFamily.sets at hB

      have hBor: (F.sets B ∧ ¬ x ∈ B) ∨ B = F.ground.erase x := by
        simpa using hB
      simp only [decide_eq_false_iff_not]
      match hBor with
      | Or.inl ⟨hB_set, hB_not_in_x⟩ => -- (F.sets s ∧ ¬ x ∈ s)
          left
          --goal F.sets A = true ∧ x ∉ A
          have B_neq_ground: B ≠ F.ground := by
          --これはx ∉ Bだけど、x ∈ F.groundなので、B ≠ F.ground
            by_contra hB_eq_ground
            rw [hB_eq_ground] at hB_not_in_x
            contradiction
          have FsetsA: F.sets A := by
            exact F.down_closed A B hB_set B_neq_ground hAB
          have hA_not_in_x: ¬ x ∈ A := λ hA_mem_x => hB_not_in_x (Finset.mem_of_subset hAB hA_mem_x)
          exact ⟨FsetsA, hA_not_in_x⟩

        | Or.inr hB_eq => -- B = F.ground.erase x
          right
          contradiction

    inc_ground :=  λ s hs => by
        simp_all only [decide_eq_false_iff_not]
        cases hs with
        | inl hl =>
          have hs'' : s ⊆ F.ground := F.inc_ground s hl.1
          exact Finset.subset_erase.2 ⟨hs'', hl.2⟩
        | inr hr => --全体集合のケース s = F.ground.erase x
          rw [hr],

    has_empty :=
      by
        --deletionしても空集合は残る。
        have emp: F.sets ∅ := F.has_empty
        unfold SetFamily.sets at emp
        simp_all only [decide_eq_false_iff_not]
        rw [IdealFamily.toSetFamily] at emp
        simp,

    has_ground := -- univ = F.ground.erase x
      by
        let newsets := λ s => (F.sets s ∧ ¬ x ∈ s) ∨ s = F.ground.erase x
        have ss: newsets (F.ground.erase x):= by
          right
          rfl
        unfold SetFamily.sets at ss
        simp_all only [decide_eq_false_iff_not]
        rw [IdealFamily.toSetFamily]
        simp,

    nonempty_ground := ground_nonempty_after_minor F.ground x hx ground_ge_two,
}

-- Contraction操作の定義
def contraction (F : SetFamily α) (x : α) (hx : x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2): SetFamily α :=
  { ground := F.ground.erase x,

    sets := λ (s: Finset α) => ∃ (H :Finset α), F.sets H ∧ x ∈ H ∧ s = H.erase x,

    inc_ground := by
        intros s hs
        rcases hs with ⟨H, hH_sets, _, hs_eq⟩
        rw [hs_eq]
        --goal H.erase x ⊆ F.ground.erase x
        intro y hy -- hy: y ∈ H.erase x
        rw [Finset.mem_erase] at hy
        rw [Finset.mem_erase]
        -- goal y ≠ x ∧ y ∈ F.ground
        constructor
        exact hy.1 -- x ¥neq y
        apply F.inc_ground H hH_sets-- H ⊆ F.ground
        exact hy.2 --y ∈ H


    nonempty_ground := ground_nonempty_after_minor F.ground x hx ground_ge_two
  }

-- IdealFamilyに対するcontraction操作がIdealFamilyになることの証明
instance contraction_ideal_family (F : IdealFamily α) (x : α) (hx : F.sets {x} ) (ground_ge_two: F.ground.card ≥ 2): IdealFamily α :=
{
  contraction (F.toSetFamily) x (by { exact F.inc_ground {x} hx (by simp) }) ground_ge_two with
  has_empty := by
    use {x}
    constructor
    exact hx -- goal F.sets {x}
    constructor
    simp
    simp

  has_ground := by
    use F.ground
    constructor
    exact F.has_ground
    constructor
    -- goal x ∈ F.ground
    exact F.inc_ground {x} hx (by simp)
    rfl

  --(down_closed : ∀ (A B : Finset α), sets B → B ≠ ground → A ⊆ B → sets A)
  --Fのdown_closedを使って、contractionのdown_closedを証明する。
  down_closed := by
    let thisF := contraction (F.toSetFamily) x (by { exact F.inc_ground {x} hx (by simp) }) ground_ge_two
    have thisg : thisF.ground = F.ground.erase x := by
        rfl
    have thisinc: thisF.ground ⊆ F.ground := by
      rw [thisg]
      apply Finset.erase_subset

    have groundx: F.ground = thisF.ground ∪ {x} := by
      ext y
      constructor
      -- x ∈ F.groundのとき
      intro hy
      by_cases hxy: x = y
      -- x = yのとき
      rw [hxy]
      simp
      -- x ≠ yのとき
      rw [Finset.mem_union, Finset.mem_singleton]
      left

      rw [thisg]
      rw [Finset.mem_erase]
      simp
      constructor
      tauto
      exact hy

      -- y ∈ thisF.ground ∨ y = x → y ∈ F.ground
      intro hy
      rw [Finset.mem_union, Finset.mem_singleton] at hy
      by_cases  hy' : x = y
      case pos =>
        rw [←hy']
        exact F.inc_ground {x} hx (by simp)

      case neg =>  --x neq yの場合
        --goal y ∈ F.ground
        have hinThis: y ∈ thisF.ground := by
          tauto
        --  y ∈ thisF.groundと、thisF.ground ⊆ F.groundから、y ∈ F.ground
        have y_in_F_ground : y ∈ F.ground := by
           apply Finset.mem_of_subset thisinc hinThis
        exact y_in_F_ground

    intros A B hB hB_ne_ground hAB
    have thisF_sets: thisF.sets B := hB
    obtain ⟨H, _, _, hB_eq⟩ := hB

    have nxB: x ∉ B := by --この理由はgroundでなくて、sets Bの定理より。
      rw [hB_eq]
      exact Finset.not_mem_erase x H

    have nxA: x ∉ A := by
      by_contra h
      have hxB: x ∈ B := by
        apply hAB
        exact h
      contradiction

    have sets_imp: thisF.sets B → F.sets (B ∪ {x}) := by
      intro hB_sets --introをhaveの外に出す。TODO
      obtain ⟨H, hH_sets, hxH, hB_eq⟩ := hB_sets --TODO obtainをhaveの外に出すと良い。

      have h_union : H = (B ∪ {x}) := by
        rw [hB_eq]
        rw [Finset.union_comm]
        rw [←Finset.insert_eq]
        rw [Finset.insert_erase]
        exact hxH
      rwa [← h_union]

    have Fsets: F.sets (B ∪ {x}) := by
      apply sets_imp
      exact thisF_sets

    have Fsets_down: F.sets (A ∪ {x}) := by
      apply F.down_closed (A ∪ {x}) (B ∪ {x})
      exact Fsets
      intro h--h : B ∪ {x} = F.ground
      rw [groundx] at h
      -- h  B ∪ {x} = thisF.ground ∪ {x}
      apply hB_ne_ground
      -- goal B = thisF.ground
      have nthisF: x ∉ thisF.ground := by
        dsimp [thisF]
        dsimp [contraction]
        rw [Finset.erase_eq]
        simp
      have hB_eq: B = thisF.ground := by
        ext y
        constructor
        -- y ∈ B → y ∈ thisF.ground
        intro hy
        have xneqy: x ≠ y := by
          intro hxy
          rw [←hxy] at hy
          contradiction
        -- h: B ∪ {x} = thisF.ground ∪ {x}
        have hyy: y ∈ thisF.ground ∪ {x}:= by
          rw [←h]
          apply Finset.mem_union_left
          exact hy
        --rw [←h] at hyy
        rw [Finset.mem_union] at hyy
        --hyy : y ∈ thisF.ground ∨ y = xだが、xneqyからy ∈ thisF.ground
        cases hyy with
        | inl hyy' =>
          exact hyy'
        | inr hyy' =>
          --xneqy： x ≠ yとhyy' : y in {x}から矛盾
          rw [Finset.mem_singleton] at hyy'
          rw [hyy'] at xneqy
          contradiction
        --y ∈ thisF.ground → y ∈ B
        intro hy
        have hyy: y ∈ thisF.ground ∪ {x} := by
          apply Finset.mem_union_left
          exact hy
        rw [←h] at hyy
        rw [Finset.mem_union] at hyy
        cases hyy with
        | inl hyy' =>
          exact hyy'
        | inr hyy' =>
          rw [Finset.mem_singleton] at hyy'
          --rw [←hyy'] at nxB
          rw [hyy'] at hy
          contradiction

      rw [hB_eq]
      exact Finset.union_subset_union hAB (by simp)

    have thisF_setsA: thisF.sets A := by
      dsimp [thisF]
      unfold contraction
      unfold SetFamily.sets

      have thisFset: (s : Finset α) → thisF.sets s ↔ ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x:= by
        unfold SetFamily.sets
        dsimp [thisF]
        rw [contraction]
        simp
      have existsH: ∃ H, F.sets H ∧ x ∈ H ∧ A = H.erase x := by
        use  A ∪ {x}
        constructor
        exact Fsets_down
        simp
        show A  = (A ∪ {x}).erase x
        rw [Finset.union_comm]
        rw [←Finset.insert_eq]
        rw [Finset.erase_insert nxA]
      exact (thisFset A).mpr existsH
    exact thisF_setsA
}

lemma ground_deletion  (F : IdealFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2):
  (idealdeletion F x hx ground_ge_two).ground.card = F.ground.card - 1 :=

  by
    rw [idealdeletion]
    rw [Finset.card_erase_of_mem hx]

lemma ground_contraction  (F : IdealFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2):
  (contraction F.toSetFamily x hx ground_ge_two).ground.card = F.ground.card - 1 :=
  by
    rw [contraction]
    rw [Finset.card_erase_of_mem hx]

lemma ground_contraction_family  (F : IdealFamily α) (x : α) (ground_ge_two: F.ground.card ≥ 2)(singleton_have: F.sets {x}):
  (contraction_ideal_family F x singleton_have ground_ge_two).ground.card = F.ground.card - 1 :=
  by
    rw [contraction_ideal_family]
    rw [ground_contraction]

end Ideal
