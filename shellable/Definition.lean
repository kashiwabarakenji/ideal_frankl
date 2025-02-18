import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import LeanCopilot

variable {V : Type} [Fintype V]

-- Prop への関数としての単体的複体の定義
structure SimplicialComplex (V : Type) [Fintype V] where
  faces : Finset V → Prop
  downward_closed : ∀ {σ τ : Finset V}, faces σ → τ ⊆ σ → τ ≠ ∅ → faces τ

noncomputable instance decidableFaces (Δ : SimplicialComplex V) : DecidablePred Δ.faces :=
  fun σ => Classical.propDecidable (Δ.faces σ)

/-- 単体（有限部分集合）の次元を「|σ| - 1」と定義する。 -/
def faceDim (σ : Finset V) : ℕ :=
  σ.card - 1

noncomputable def dim (Δ : SimplicialComplex V) : ℕ :=
  -- Finset.sup を使って「複体に属するすべての面の次元」の最大値を計算
  Finset.sup
    (Finset.filter Δ.faces (Finset.powerset Finset.univ))
    faceDim

/--
  `σ` が複体 `Δ` のファセット (facet) であるとは、
  1) `σ` が `Δ` に属し、
  2) それより大きい（包含関係で真に含む）面が存在しない
  こと。
-/
def isFacet (Δ : SimplicialComplex V) (σ : Finset V) : Prop :=
  Δ.faces σ ∧ ∀ τ, σ ⊆ τ → Δ.faces τ → σ = τ

/-- `Δ` のファセット全体を Finset として取り出す例。 -/
noncomputable def facets (Δ : SimplicialComplex V) : Finset (Finset V) :=
  (Finset.filter (fun σ => (Classical.propDecidable (isFacet Δ σ)).decide)
    (Finset.filter Δ.faces (Finset.powerset Finset.univ)))

/--
  複体 `Δ` が純 (pure) であるとは、すべてのファセットが同じ次元を持つこと。

  ここでは「次元 = `dim Δ`」を持つファセットしかない、という形で定義している。
-/
def isPure (Δ : SimplicialComplex V) : Prop :=
  let d := dim Δ
  ∀ (F:Finset V),F ∈ facets Δ→ faceDim F = d


/- ここから下がシェラビリティに関する定義 -/

/--
  ファセットの並び（リスト）に対して、
  「先に並べたファセットからなる複体」と「次のファセット」との交わりが
  （次元 `d - 1` の）純な部分複体になることを要求する“シェリング条件”の例。

  実際には「リストの j 番目のファセット `F_j` と、それ以前に並べたファセットの合併複体 `Δ_{<j}`」の
  交わり (subcomplex) が `(d - 1)` 次元で純になっていることを言いたい。

  ここでは型を合わせるために `sorry` や「subcomplex の定義」を省略している。
-/
def subcomplexFromFacets (Δ : SimplicialComplex V) (fs : List (Finset V)) :
    SimplicialComplex V :=
  {
    faces := λ σ => ∃ F ∈ fs, (Δ.faces F) ∧ (σ ⊆ F),
    downward_closed := by
      -- 下向き閉包性を示す: もし σ が顔なら，その部分集合 τ ⊆ σ も顔
      rintro σ τ ⟨F, hF_in_fs, hF_in_Δ, hσF⟩ hτσ hτ_nonempty
      -- τ ⊆ F かつ F ∈ Δ.faces なので τ も Δ.faces に属する（Δ.downward_closed より）
      have hτ_in_Δ : Δ.faces τ := Δ.downward_closed hF_in_Δ (hτσ.trans hσF) hτ_nonempty
      exact ⟨F, hF_in_fs, hF_in_Δ, hτσ.trans hσF⟩
  }

  def restrictComplex (Δ : SimplicialComplex V) (S : Finset V) : SimplicialComplex V :=
  {
    faces := λ σ => Δ.faces σ ∧ σ ⊆ S,
    downward_closed := by
      rintro σ τ ⟨hσ_in_Δ, hσS⟩ hτσ hτ_nonempty
      -- τ ⊆ S かつ Δ.faces τ であることを示す
      have hτ_in_Δ : Δ.faces τ := Δ.downward_closed hσ_in_Δ hτσ hτ_nonempty
      exact ⟨hτ_in_Δ, hτσ.trans hσS⟩
  }

def isPureOfDim (d : ℕ) (Δ : SimplicialComplex V) : Prop :=
  (dim Δ = d) ∧ (isPure Δ)

def shellingCondition
  (Δ : SimplicialComplex V)
  (F : List (Finset V)) -- ファセットを並べたリスト
  (d : ℕ)              -- 複体の次元
  : Prop :=
  ∀ j, (h1:1 < j) → (h2:j ≤ F.length) →
    let idx : Fin F.length := ⟨ j-1, by
      -- 以下、j ≤ F.length と 1 < j から j-1 < F.length を証明
      apply Nat.lt_of_lt_of_le (Nat.pred_lt (Nat.succ_ne_zero _))
      simp_all only [Nat.succ_eq_add_one]
      omega
    ⟩
    let currentFacet := F.get idx
    let prevFacets := F.take (j-1)
    let Δprev := subcomplexFromFacets Δ prevFacets
    -- Δprev と currentFacet の交わりを計算
    let intersection := restrictComplex Δprev currentFacet
    -- ここで「intersection が (d-1) 次元の純な複体になっている」ことを要求
    isPureOfDim (d - 1) intersection

/--
  複体 `Δ` がシェラブルであるとは、
  あるファセット列（全てのファセットを並べたものの並び替え `F`）が存在して、
  上記の `shellingCondition` をみたすこと。
-/
def isShellable (Δ : SimplicialComplex V) : Prop :=
  let d := dim Δ
  ∃ (F : List (Finset V)),
    -- 1) F が Δ のファセットをちょうど並べたリストである（同じ要素・順番のみ違う）
    F.Perm (facets Δ).toList ∧
    -- 2) シェリング条件を満たす
    shellingCondition Δ F d
