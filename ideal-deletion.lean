import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Mathlib.Init.Function
import Mathlib.Init.Logic
import LeanCopilot

-- 型変数と必要な型クラスの宣言 この宣言は必要。もともとUだったのをαに変えた。
variable {α : Type} [DecidableEq α] [Fintype α][Nonempty α]

structure SetFamily (α : Type) :=
  (ground : Finset α)  -- 全体集合
  (sets : Finset α → Prop)  -- 集合族を定義する関数
  (inc_ground : ∀ s, sets s → s ⊆ ground)  -- 全体集合に含まれることを保証
  (nonempty_ground : ground.Nonempty)

open Finset

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

def deletion {α : Type} [DecidableEq α] (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2): SetFamily α :=
  { ground := F.ground.erase x,
    sets := λ s => F.sets s ∧ ¬ x ∈ s,
    nonempty_ground := ground_nonempty_after_deletion F.ground x hx gcard
    /-      by
        rw [Finset.erase_eq]
        apply Finset.nonempty_of_ne_empty
        by_contra h_empty
        by_cases hA : F.ground = ∅
        rw [hA] at gcard
        --使わなかったからコメントアウト
        --have _: F.ground.card = 0 := by
        --  rw [hA]
        --  exact Finset.card_empty
        contradiction

        --F.ground.card = 1のケース
        have g_eq_x: F.ground = {x} := by
          --h_empty : F.ground \ {x} = ∅
          --¬F.ground = ∅
          ext y
          constructor
          intro hy
          have hy' : y ∈ F.ground \ {x} := by
            rw [h_empty]
            simp_all only [ge_iff_le, sdiff_eq_empty_iff_subset, subset_singleton_iff, false_or, singleton_ne_empty,
              not_false_eq_true, mem_singleton, not_mem_empty, card_singleton, Nat.not_ofNat_le_one]
          rw [h_empty] at hy'
          contradiction

          --y ∈ {x}のときに、F.groundに属することを示す
          intro hy
          have x_eq_y : x = y := by
            rw [mem_singleton] at hy
            rw [hy]
          rw [x_eq_y] at hx
          exact hx

        rw [g_eq_x] at gcard
        rw [Finset.card_singleton] at gcard
        contradiction
    -/

    inc_ground :=

      λ s hs => by
        --rename_i inst
        simp_all only [Bool.decide_and, Bool.decide_eq_true, decide_not, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not]
        obtain ⟨left, right⟩ := hs
        have hs' : s ⊆ F.ground := F.inc_ground s left
        exact subset_erase.2 ⟨hs', right⟩
        --theorem Finset.subset_erase {α : Type u_1}  [DecidableEq α]  {a : α}  {s : Finset α}  {t : Finset α} :
        --s ⊆ Finset.erase t a ↔ s ⊆ t ∧ a ∉ s
        }

infixl:65 " ∖ " => deletion

structure IdealFamily (α : Type) [DecidableEq α] [Fintype α] extends SetFamily α :=
(empty_mem : sets ∅)  -- 空集合が含まれる
(univ_mem : sets ground)  -- 全体集合が含まれる
(down_closed : ∀ (A B : Finset α), sets B → B ≠ ground → A ⊆ B → sets A)

def idealdeletion {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2): IdealFamily α :=
{
    ground := F.ground.erase x,

    sets := λ s => (F.sets s ∧ ¬ x ∈ s) ∨ s = F.ground.erase x,

    --(down_closed : ∀ {A B : Finset α}, sets B → B ≠ ground → A ⊆ B → sets A)
    down_closed := λ A B hB hB_ne_ground hAB => by
      unfold SetFamily.sets at hB

      have hBor: (F.sets B ∧ ¬ x ∈ B) ∨ B = F.ground.erase x := by
        simpa using hB
      simp_all only [Bool.decide_and, Bool.decide_eq_true, decide_not, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, Bool.or_eq_true]
      --rw [decide_eq_true_eq] setsの値がtrueかfalseであるのをPropに変換する
      match hBor with
      | Or.inl ⟨hB_set, hB_not_in_x⟩ => -- (F.sets s ∧ ¬ x ∈ s)
          --hB_set : F.sets B = true
          -- hB_not_in_x : x ∉ B
          left
          --goal F.sets A = true ∧ x ∉ A
          have B_neq_ground: B ≠ F.ground := by
          --これはx ∉ Bだけど、x ∈ F.groundなので、B ≠ F.ground
            by_contra hB_eq_ground
            rw [hB_eq_ground] at hB_not_in_x
            contradiction
          have FsetsA: F.sets A := by
            exact F.down_closed A B hB_set B_neq_ground hAB
          have hA_not_in_x: ¬ x ∈ A := λ hA_mem_x => hB_not_in_x (mem_of_subset hAB hA_mem_x)
          exact ⟨FsetsA, hA_not_in_x⟩

        | Or.inr hB_eq => -- B = F.ground.erase x
          right
          contradiction

    inc_ground :=  λ s hs => by
        simp_all only [Bool.decide_and, Bool.decide_eq_true, decide_not, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not, Bool.or_eq_true]
        --rw [decide_eq_true_eq] at hs setsの値がtrueかfalseであるのをPropに変換する
        --#check hs -- F.sets s = true ∧ x ∉ s ∨ s = F.ground.erase x
        cases hs with
        | inl hl =>
          --#check hl --F.sets s = true ∧ x ∉ s

          --#check hl.1
          --#check hl.2
          have hs'' : s ⊆ F.ground := F.inc_ground s hl.1
          exact subset_erase.2 ⟨hs'', hl.2⟩
        | inr hr => --全体集合のケース s = F.ground.erase x
          --#check hr -- hr : s = F.ground.erase x
          rw [hr],

    empty_mem :=
      by
        --deletionしても空集合は残る。
        have emp: F.sets ∅ := F.empty_mem
        unfold SetFamily.sets at emp
        simp_all only [Bool.decide_eq_true, decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
        --#check emp --emp : F.toSetFamily.2 ∅ = true
        rw [IdealFamily.toSetFamily] at emp
        --#check emp -- emp : F.1.2 ∅ = true
        simp,

    univ_mem := -- univ = F.ground.erase x
      by
        let newsets := λ s => (F.sets s ∧ ¬ x ∈ s) ∨ s = F.ground.erase x
        have ss: newsets (F.ground.erase x):= by
          right
          rfl
        unfold SetFamily.sets at ss
        simp_all only [Bool.decide_eq_true, decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
        rw [IdealFamily.toSetFamily]
        simp,

    nonempty_ground := ground_nonempty_after_deletion F.ground x hx gcard,
}

-- Contraction操作の定義
def contraction (F : SetFamily α) (x : α) (hx : x ∈ F.ground) (gcard: F.ground.card ≥ 2): SetFamily α :=
  { ground := F.ground.erase x,

    sets := λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x,

    inc_ground := by
        intros s hs
        rcases hs with ⟨H, hH_sets, _, hs_eq⟩
        rw [hs_eq]
        --#check hH_sets -- F.sets H
        --#check hs_eq --s = H.erase x
        --goal H.erase x ⊆ F.ground.erase x
        intro y hy -- hy: y ∈ H.erase x
        rw [mem_erase] at hy
        rw [mem_erase]
        -- goal y ≠ x ∧ y ∈ F.ground
        constructor
        exact hy.1 -- x ¥neq y
        apply F.inc_ground H -- H ⊆ F.ground
        exact hH_sets -- F.sets H
        exact hy.2 --y ∈ H
        --なぜexactが3つもあるのか。

    nonempty_ground := ground_nonempty_after_deletion F.ground x hx gcard
  }

-- IdealFamilyに対するcontraction操作がIdealFamilyになることの証明
instance contraction_ideal_family (F : IdealFamily α) (x : α) (hx : F.sets {x} ) (gcard: F.ground.card ≥ 2): IdealFamily α :=
{
  contraction (F.toSetFamily) x (by { exact F.inc_ground {x} hx (by simp) }) gcard with
  empty_mem := by
    use {x} -- emptyを使うべきではなく、これが正解っぽい。
    constructor
    exact hx -- goal F.sets {x}
    constructor
    simp
    simp

  univ_mem := by
    use F.ground
    constructor
    exact F.univ_mem
    constructor
    -- goal x ∈ F.ground
    exact F.inc_ground {x} hx (by simp)
    rfl

  --(down_closed : ∀ (A B : Finset α), sets B → B ≠ ground → A ⊆ B → sets A)
  --Fのdown_closedを使って、contractionのdown_closedを証明する。
  down_closed := by
  {
    let thisF := contraction (F.toSetFamily) x (by { exact F.inc_ground {x} hx (by simp) }) gcard
    --証明が不完全。あとで使うかも。
    have groundx: F.ground = thisF.ground ∪ {x} := by
      ext y
      constructor
      intro hy
      by_cases hxy: x = y
      rw [hxy]
      simp

      -- x ≠ yのとき
      rw [Finset.mem_union, Finset.mem_singleton]
      left
      have thisg : thisF.ground = F.ground.erase x := by
        rfl
      rw [thisg]
      rw [Finset.mem_erase]

      constructor
      by_contra h
      rw [h] at hxy
      contradiction
      exact hy

    intros A B hB hB_ne_ground hAB
    /-つかわなかったし、証明も不完全。けして良い。
    --以下の補題は、thisF.sets Bの前提のもので成り立つ。
    have hB_sets0: ∃ H, F.sets H ∧ x ∈ H ∧ B = H.erase x := by
     -- Bがcontraction後の集合族に属するという前提から、Hを見つける
      simp only [groundx] at hB
      --goal ∃ H, F.sets H ∧ x ∈ H ∧ B = H.erase x
      --Fのfd.down_closedを使って、証明する。
      -- (contraction F.toSetFamily x ⋯ gcard).sets B
      exact F.down_closed B (B ∪ {x}) hB hB_ne_ground (by
        intro h_eq
        rw [h_eq] at hAB
        contradiction
      )
    -/

    have sets_imp: thisF.sets B → F.sets (B ∪ {x}) := by
      intro hB_sets
      have ninB: x ∉ B := by simp [hB_sets.2.2]
      obtain ⟨H, hH_sets, hxH, hB_eq⟩ := hB_sets
      --hB_sets : F.sets H
      --hxB : x ∈ H
      --hB_eq : B = H.erase x
      have h_union : H = (B ∪ {x}) := by
        rw [hB_eq]
        rw [union_comm]
        rw [←Finset.insert_eq]
        rw [Finset.insert_erase]
        exact hxH
      rwa [← h_union]


    have thisF_sets: thisF.sets B := hB

    have Fsets: F.sets (B ∪ {x}) := by
      apply sets_imp
      exact thisF_sets

    --ここで夏学のために休止。
    --F.sets (A cup {x})がF.setsのdown_closedからいえる。
    --するとcontractionの定義から、contraction後のsets Aがいえる。
    have Fsets_down: F.sets (A ∪ {x}) := by
      apply F.down_closed (A ∪ {x}) (B ∪ {x})
      exact Fsets
      intro h
      apply hB_ne_ground
      rw [h, finset.erase_eq_of_not_mem (λ H => hxH (Finset.mem_singleton.mp H))]
      exact finset.ext (λ y=> ⟨λ hy=> finset.mem_insert_of_mem _ hy, λ hy=> finset.mem_of_mem_insert_of_ne hy (finset.not_mem_erase x y)⟩)
      exact hAB

    have contraction_sets_A: thisF.sets A := by
      rw [contraction]
      rw [set_family.mk_sets]
      exact Fsets_down

    exact contraction_sets_A
  }
}
--この関数のために、setsの値をBoolからPropに変換する。
def total_size_of_hyperedges (F : SetFamily α)  [DecidablePred F.sets] : ℕ :=
  let all_sets := (Finset.powerset F.ground).filter F.sets
  all_sets.sum Finset.card

def number_of_hyperedges (F : SetFamily α) [DecidablePred F.sets] : ℕ :=
  let all_sets := (Finset.powerset F.ground).filter F.sets
  all_sets.card

def standardized_degree_sum (F : SetFamily α) [DecidablePred F.sets] : ℕ :=
  total_size_of_hyperedges F - 2 * number_of_hyperedges F
