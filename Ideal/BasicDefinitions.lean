import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
--import Mathlib.Algebra.BigOperators.Basic
--import Mathlib.Algebra.BigOperators.Group.Finset
--import Mathlib.Init.Data.Nat.Lemmas
--import Mathlib.Data.Bool.Basic
--import Mathlib.Tactic
--import LeanCopilot

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α]-- [Nonempty α] コメントアウトしてみた。

--集合族の定義
structure SetFamily (α : Type) [DecidableEq α]  where
  (ground : Finset α)
  (sets : Finset α → Prop)
  (inc_ground : ∀ s, sets s → s ⊆ ground)
  (nonempty_ground : ground.Nonempty)
  [fintype_ground : Fintype ground]

--Ideal集合族の定義
structure IdealFamily (α : Type) [DecidableEq α] [Fintype α] extends SetFamily α where
(has_empty : sets ∅)  -- 空集合が含まれる
(has_ground : sets ground)  -- 全体集合が含まれる
(down_closed : ∀ (A B : Finset α), sets B → B ≠ ground → A ⊆ B → sets A)

--この関数のために、setsの値をBoolからPropに変換する。
def total_size_of_hyperedges (F : SetFamily α)  [DecidablePred F.sets] : ℕ :=
  ∑ x ∈ ((Finset.powerset F.ground).filter F.sets), x.card

--集合族のhyperedgeの個数
def number_of_hyperedges (F : SetFamily α) [DecidablePred F.sets] : ℕ :=
  ((Finset.powerset F.ground).filter F.sets).card

--頂点の次数を計算する関数 これはZにしなくてもよい？
noncomputable def degree (sf : SetFamily α) (v : α) : ℕ :=
  Finset.card (Finset.filter (λ s => sf.sets s = true ∧ v ∈ s) (sf.ground.powerset))

-- 空集合がセットに含まれることを定義
def has_empty (sf : SetFamily α) : Prop :=
  sf.sets ∅

-- 全体集合がセットに含まれることを定義
def has_univ (sf : SetFamily α) : Prop :=
  sf.sets Finset.univ

-- hyperedgeがが共通部分に対して閉じていることを定義
def is_closed_under_intersection (sf : SetFamily α) : Prop :=
  ∀ (A B : Finset α), sf.sets A → sf.sets B → sf.sets (A ∩ B)

-- 頂点がレアであることを定義
def is_rare (sf : SetFamily α) (v : α)  [DecidablePred sf.sets]  : Prop :=
  2 * degree sf v ≤ number_of_hyperedges sf

-- Ideal Family の条件を定義
def is_ideal (sf : SetFamily α) : Prop :=
  has_empty sf ∧ has_univ sf ∧
  (∀ (A B : Finset α), sf.sets B → A ⊆ B → sf.sets A)

-- DecidablePredインスタンスの提供 なくすとnormalized_degree_sumでエラーが出る。SetFamilyに対して、定義しなくて良いのか？
noncomputable instance [DecidableEq α] (sf : IdealFamily α) : DecidablePred sf.sets :=
λ s => Classical.propDecidable (sf.sets s)

noncomputable instance [DecidableEq α] (sf : SetFamily α) : DecidablePred sf.sets :=
λ s => Classical.propDecidable (sf.sets s)

-- 標準化次数和を計算する関数を定義 上のinstanceの定義のあとにする必要あり。
-- IdealFamilyでない場合に定義する。
noncomputable def normalized_degree_sum {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) [DecidablePred F.sets] : ℤ :=
  let total_size := (total_size_of_hyperedges F: ℤ)
  let num_sets := (number_of_hyperedges F: ℤ)
  let base_set_size := (F.ground.card: ℤ)
  total_size * 2 - num_sets * base_set_size

-- Ideal_family_size_sf関数の定義 必要なのか？
noncomputable def ideal_family_size (sf : IdealFamily α) : ℕ :=
number_of_hyperedges sf.toSetFamily

-- Ideal Family の頂点の次数を計算する関数。必要ない気もするが、現状では使っている。
noncomputable def ideal_degree (sf : IdealFamily α) (x : α) : ℕ :=
  degree (sf.toSetFamily) x

--IntersectionClosedFamilyの定義
structure IntersectionClosedFamily (α : Type) [DecidableEq α] [Fintype α] extends SetFamily α where
  (has_ground : sets ground)  -- 全体集合が含まれる
  (intersection_closed : ∀ {s t : Finset α}, sets s→ sets t → sets (s ∩ t) ) -- 条件2: 共通部分で閉じている

end Ideal
