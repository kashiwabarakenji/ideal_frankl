import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic
import LeanCopilot

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

structure SetFamily (α : Type) [DecidableEq α] [Fintype α] :=
  (ground : Finset α)
  (sets : Finset α → Prop)
  (inc_ground : ∀ s, sets s → s ⊆ ground)
  (nonempty_ground : ground.Nonempty)

-- SetFamily 構造体の定義 Boolバージョン
--structure SetFamily (α : Type) :=
--  (ground : Finset α) -- 全体集合
--  (sets : (Finset α) → Bool)  -- 集合族を定義する関数
--  (inc_ground: sets s → s ⊆ ground) -- 全体集合が含まれる
--  (nonempty_ground : ground.Nonempty)

structure IdealFamily (α : Type) [DecidableEq α] [Fintype α] extends SetFamily α :=
(empty_mem : sets ∅)  -- 空集合が含まれる
(univ_mem : sets ground)  -- 全体集合が含まれる
(down_closed : ∀ (A B : Finset α), sets B → B ≠ ground → A ⊆ B → sets A)

--この関数のために、setsの値をBoolからPropに変換する。
def total_size_of_hyperedges (F : SetFamily α)  [DecidablePred F.sets] : ℕ :=
  let all_sets := (Finset.powerset F.ground).filter F.sets
  all_sets.sum Finset.card

def number_of_hyperedges (F : SetFamily α) [DecidablePred F.sets] : ℕ :=
  let all_sets := (Finset.powerset F.ground).filter F.sets
  all_sets.card

def standardized_degree_sum (F : SetFamily α) [DecidablePred F.sets] : ℕ :=
  total_size_of_hyperedges F - 2 * number_of_hyperedges F

-- 任意の型 α に対する部分集合の集合を全て列挙する関数
def all_subsets {α : Type} [DecidableEq α] (s : Finset α) : Finset (Finset α) :=
  s.powerset

noncomputable def degree (sf : SetFamily α) (v : α) : ℕ :=
  Finset.card (Finset.filter (λ s => sf.sets s = true ∧ v ∈ s) (all_subsets sf.ground))

-- 空集合がセットに含まれることを定義
def has_empty (sf : SetFamily α) : Prop :=
  sf.sets ∅

-- 全体集合がセットに含まれることを定義
def has_univ (sf : SetFamily α) : Prop :=
  sf.sets Finset.univ

-- セットが交差に対して閉じていることを定義
def is_closed_under_intersection (sf : SetFamily α) : Prop :=
  ∀ (A B : Finset α), sf.sets A → sf.sets B → sf.sets (A ∩ B)

-- 頂点がレアであることを定義
def is_rare (sf : SetFamily α) (v : α)  [DecidablePred sf.sets]  : Prop :=
  2 * degree sf v ≤ number_of_hyperedges sf

-- Ideal Family の条件を定義
def is_ideal (sf : SetFamily α) : Prop :=
  has_empty sf ∧ has_univ sf ∧
  (∀ (A B : Finset α), sf.sets B → A ⊆ B → sf.sets A)

-- to_SetFamily関数の定義
--def to_SetFamily {α : Type*} (sf : SetFamily α) : SetFamily α :=
--sf

-- DecidablePredインスタンスの提供 必要なのか？
noncomputable instance [DecidableEq α] (sf : IdealFamily α) : DecidablePred sf.sets :=
λ s => Classical.propDecidable (sf.sets s)

-- Ideal_family_size_sf関数の定義 必要なのか？
noncomputable def ideal_family_size (sf : IdealFamily α) : ℕ :=
number_of_hyperedges sf.toSetFamily

-- Ideal Family のサイズを計算する関数
--def ideal_family_size (sf : IdealFamily α)[DecidablePred (to_SetFamily sf).sets] : ℕ :=
--   number_of_hyperedges (to_SetFamily sf)

-- Ideal Family の頂点の次数を計算する関数
noncomputable def ideal_degree (sf : IdealFamily α) (x : α) : ℕ :=
  degree (sf.toSetFamily) x
