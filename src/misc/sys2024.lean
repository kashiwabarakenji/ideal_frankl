--具体的な集合族に対して、次数や最小次数を計算するプログラム
--Finsetだとcomputableの関係でうまくいかないので、Listを使っている
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm

-- 集合族を定義（リストのリストとして表現）
structure SetFamily :=
  sets : List (List Nat)
deriving Repr

-- 共通部分を計算します
def isClosedUnderIntersection (sf : SetFamily) : Bool :=
  sf.sets.all (fun A =>
    sf.sets.all (fun B =>
      sf.sets.contains (A.filter (fun x => B.contains x))))

-- すべての部分集合を生成する関数
def powersetList (list : List Nat) : List (List Nat) :=
  let rec aux : List Nat → List (List Nat)
    | [] => [[]]
    | (h :: t) =>
      let withoutH := aux t
      let withH := withoutH.map (h :: ·)
      withoutH ++ withH
  aux list

-- 部分集合族の具体的な例を定義
def example_set_family : SetFamily :=
  let allSets := powersetList [0, 1, 2, 3, 4, 5]
  ⟨allSets.filter (λ s => s.length ≥ 3)⟩

def example_set_family2 : SetFamily :=
  { sets := [ [1, 2, 3, 4, 5], [4, 5, 6], [1, 4, 5], [2, 4, 5], [4, 5], [0, 4] ] }


-- 各点の次数を計算する関数を定義
def degree (sf : SetFamily) (v : Nat) : Nat :=
  (sf.sets.filter (λ s => v ∈ s)).length

-- 全ての点に対して次数を計算し、リストとして表示する関数を定義
def degrees_list (sf : SetFamily) : List (Nat × Nat) :=
  [0, 1, 2, 3, 4, 5].map (λ v => (v, degree sf v))

def allVertices : List Nat := [0, 1, 2, 3, 4, 5]

def vertexDegrees (sf : SetFamily) : List (Nat × Nat) :=
  allVertices.map (fun v => (v, degree sf v))

-- リスト内の最小値を計算する関数
def listMinimum (l : List Nat) : Nat :=
  l.foldl Nat.min (l.headD 0)

-- 最小次数を計算する
def minDegree (sf : SetFamily) : Nat :=
  listMinimum ((vertexDegrees sf).map Prod.snd)

-- 集合族の要素をリストとして表示
def display_all_elements (sf : SetFamily) : List (List Nat) :=
  sf.sets

-- メイン関数
def main : IO Unit := do
  IO.println s!"集合族の要素: {display_all_elements example_set_family}"
  IO.println s!"各点の次数: {degrees_list example_set_family}"
  IO.println s!"最小次数: {minDegree example_set_family}"

def main2 : IO Unit := do
  IO.println s!"集合族の要素: {display_all_elements example_set_family2}"
  IO.println s!"各点の次数: {degrees_list example_set_family2}"
  IO.println s!"最小次数: {minDegree example_set_family2}"

#eval main

#eval main2
