--Ideal集合族が平均abundantにならないことの証明が目標。まだうまく行ってないが保留にする。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import Ideal.IdealDeletion
import Ideal.IdealRare
import Ideal.IdealSum
import Ideal.IdealNumbers
import LeanCopilot

-- 必要なインポート
import Mathlib.Data.Set.Basic
namespace Ideal
open Finset

-- 定理のステートメント
theorem injective_image_injective {α β : Type} [DecidableEq α] [DecidableEq β]
  (s : Finset α) (f : α → β) (hf : Function.Injective f) :
  Function.Injective (λ x : α=> f x) :=
  hf

open Std

-- finExpand の定義
def finExpand {n : ℕ} (v : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if h : x.val < v.val then
    ⟨x.val,by omega⟩
  else
    ⟨x.val + 1,by omega⟩

-- finExpand が単射であることの証明
theorem finExpand_injective {n : ℕ} (v : Fin (n + 1)) :
  Function.Injective (finExpand  v) :=
  fun x y hxy =>
    by
      unfold finExpand at hxy
      split_ifs at hxy
      -- ケース 1: 両方の x.val, y.val < v.val の場合
      simp_all only [ge_iff_le, Fin.mk.injEq]
      omega
      -- ケース 2: x.val < v.val, y.val >= v.val の場合
      simp_all only [ge_iff_le, Fin.mk.injEq]
      omega
      -- ケース 3: x.val >= v.val, y.val < v.val の場合
      simp_all only [ge_iff_le, Fin.mk.injEq]
      omega
      -- ケース 4: 両方の x.val, y.val >= v.val の場合
      simp_all only [ge_iff_le, Fin.mk.injEq]
      omega

-- Fin n から Fin (n + 1) への集合族の単射を構成
theorem finset_injective_expand {n : ℕ}  (v : Fin (n + 1)) :
  Function.Injective (λ x : Fin n => finExpand v x) :=
  finExpand_injective  v


def finDrop {n : ℕ} (nposi: n ≥ 1) (v : Fin (n + 1)) (x : Fin (n + 1)) : Fin n :=
  if h : x.val < v.val then
    ⟨x.val, by omega⟩
      --apply Nat.lt_succ_iff.2
      --exact Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ v.is_lt)⟩
  else
    ⟨x.val - 1, by omega⟩

-- Fin (n + 1) から Fin n への SetFamily の射影
def projectSetFamilyWithCardCondition {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (F : SetFamily (Fin (n + 1))) (v_notin : v ∉ F.ground) : SetFamily (Fin n) :=
  let newGround := F.ground.image (finDrop nposi v)
  let newSets := λ s : Finset (Fin n) => ∃ s', F.sets s' ∧ s = s'.image (finDrop nposi v)
  {
    ground := newGround,
    sets := newSets,
    inc_ground := λ s hs=> by
      obtain ⟨s', hs', rfl⟩ := hs
      rw [Finset.subset_iff]
      intro x hx
      have hx' : (finDrop nposi v x) ∈ s'.image (finDrop nposi v) := by
        rw [Finset.mem_image] at hx
        rcases hx with ⟨y, hy, rfl⟩
        simp_all only [Fin.coe_eq_castSucc, mem_image]
        by_cases h : y.val < v.val
        case pos =>
          use y
          simp_all only [Fin.coe_eq_castSucc, mem_image]
          constructor
          simp
          simp_all only [Fin.val_fin_lt]
          simp [finDrop, v_notin]
          simp_all only [↓reduceDIte, Fin.val_fin_lt, ↓reduceIte]
        case neg =>
          search_proof
          use ⟨y.val + 1, by
          simp_all only [Fin.val_fin_lt, not_lt, add_lt_add_iff_right]
          sorry⟩
          simp_all only [Fin.coe_eq_castSucc, mem_image]
          exact ⟨hy, by simp [h]⟩
      rw [Finset.mem_image] at hx'
      rcases hx' with ⟨y, hy, heq⟩
      have : y = x := Fin.eq_of_val_eq heq
      subst this
      exact Finset.mem_image_of_mem _ hy,
    nonempty_ground := by
      obtain ⟨g, hg⟩ := F.nonempty_ground
      exact ⟨finDrop nposi v g, Finset.mem_image_of_mem _ hg⟩,
    fintype_ground := by Finset.fintype newGround
  }

-- SetFamily (Fin (n + 1)) から SetFamily (Fin n) への射影
def projectSetFamilyUsingDrop {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (F : SetFamily (Fin (n + 1))) : SetFamily (Fin n) :=
  let newGround := F.ground.image (finDrop nposi v)
  let newSets := λ s : Finset (Fin n) => ∃ s', F.sets s' ∧ s = s'.image (finDrop nposi v)
  {
    ground := newGround,
    sets := newSets,
    inc_ground := λ s hs=> by
      obtain ⟨s', hs', rfl⟩ := hs
      rw [Finset.subset_iff]
      intro x hx
      have : x ∈ F.ground.image (finDrop nposi v) := by
        rw [Finset.mem_image]
        have nnposi: n + 1 >= 1 := by
          linarith
        use finDrop nnposi v x
        have hx' : (finDrop nposi v x) ∈ s'.image (finDrop nposi v) := by
          rw [Finset.mem_image]
          simp_all only [mem_image, Fin.coe_eq_castSucc]
          obtain ⟨w, h⟩ := hx
          obtain ⟨left, right⟩ := h
          subst right
          use w
          constructor
          exact left

        rw [Finset.mem_image] at hx'

        --use finDrop nnposi v x
      have hx' : (finDrop nposi v x) ∈ s'.image (finDrop nposi v) := by
        rw [Finset.mem_image]
        simp_all only [mem_image, Fin.coe_eq_castSucc]
        obtain ⟨w, h⟩ := hx
        obtain ⟨left, right⟩ := h
        subst right
        use w
        constructor
        exact left
        congr



      rw [Finset.mem_image] at hx'
      rcases hx' with ⟨y, hy, rfl⟩
      exact Finset.mem_of_mem_image hy,
    nonempty_ground := by
      obtain ⟨g, hg⟩ := F.nonempty_ground
      exact ⟨finDrop nposi v g, Finset.mem_image_of_mem _ hg⟩,
    fintype_ground := Finset.fintype_of_finset newGround
  }


-- IdealFamily (Fin (n+1)) から IdealFamily (Fin n) への射影
def projectIdealFamilyUsingDrop {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (F : IdealFamily (Fin (n + 1))) : IdealFamily (Fin n) :=
  let newGround := F.ground.image (finDrop nposi v)
  let newSets := λ s : Finset (Fin n) => ∃ s', F.sets s' ∧ s = s'.image (finDrop nposi v)
  {
    ground := newGround,
    sets := newSets,
    inc_ground := λ s hs => by
      obtain ⟨s', hs', rfl⟩ := hs
      rw [Finset.subset_iff]
      intro x hx
      have hx' : (finDrop nposi v x) ∈ s'.image (finDrop nposi v) := hx
      rw [Finset.mem_image] at hx'
      rcases hx' with ⟨y, hy, rfl⟩
      exact Finset.mem_of_mem_image hy,
    nonempty_ground := by
      obtain ⟨g, hg⟩ := F.nonempty_ground
      exact ⟨finDrop nposi v g, Finset.mem_image_of_mem _ hg⟩,
    fintype_ground := Finset.fintype_of_finset newGround,
    empty_mem := ⟨∅, F.empty_mem, Finset.image_empty⟩, -- 空集合が含まれることを保持
    univ_mem := ⟨F.ground, F.univ_mem, Finset.image_id'⟩, -- 全体集合も保持
    down_closed := λ A B hB hB_ne_ground hA_subset_B, by
      obtain ⟨B', hB', rfl⟩ := hB -- B を元の集合に戻す
      obtain ⟨A', hA', rfl⟩ := Finset.subset_image_iff.1 hA_subset_B -- A を元の集合に戻す
      exact ⟨A', F.down_closed A' B' hB' hB_ne_ground hA'⟩ -- ダウンワードクロージャを保持
  }

End Ideal
