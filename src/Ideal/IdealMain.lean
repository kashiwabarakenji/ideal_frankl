--Ideal集合族が平均abundantにならないことの証明が目標。まだうまく行ってないが保留にする。
import Mathlib.Data.Finset.Basic --hiding eq_empty_of_subset_empty
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic
--import Mathlib.Algebra.BigOperators
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import Ideal.IdealDeletion
import Ideal.IdealRare
import Ideal.IdealSum
import Ideal.IdealNumbers
import LeanCopilot
set_option maxHeartbeats 1000000

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

def finDrop {n : ℕ} (nposi: n ≥ 1) (v : Fin (n + 1)) (x : Fin (n + 1)) : Fin n :=
  if h : x.val < v.val then
    ⟨x.val, by omega⟩
  else
    ⟨x.val - 1, by omega⟩

def finExpand {n : ℕ}  (v : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if h : x.val < v.val then
    ⟨x.val, by omega⟩
  else
    ⟨x.val + 1, by omega⟩


lemma finDrop_expand_inverse {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (x : Fin n) :
  finDrop nposi v (finExpand  v x) = x := by
  unfold finDrop finExpand
  split_ifs with h
  · exact Eq.refl _
  · simp [finDrop, finExpand]
    -- ここで、finDrop (⟨x.val + 1, _⟩) = ⟨x.val, _⟩ となる
    -- よって、finDrop_expand_inverse が成立
    by_cases h' : x.val < v.val
    case pos =>
      simp_all only [ge_iff_le]
    case neg =>
      simp_all only [ge_iff_le]
      linarith
  simp_all only [not_lt, add_tsub_cancel_right, Fin.eta]

--そもそもこれは成り立たないのではないか？x=vのケースを除外する必要。
lemma finExpand_drop_inverse {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (y : Fin (n + 1)) :
  have nposi : n ≥ 1 := by omega
  y ≠ v → finExpand  v (finDrop nposi v y) = y := by
  unfold finDrop finExpand
  split_ifs with h
  · intro _ _
    simp_all only [ne_eq, Fin.eta]
  · simp
    intro a
    split
    next h_1 =>
      ext1
      simp_all only
      simp_all only [ge_iff_le, Fin.val_fin_lt, not_lt]
      omega
    next h_1 =>
      simp_all only [not_lt]
      ext1
      simp_all only
      simp_all only [ge_iff_le, Fin.val_fin_lt, not_lt]
      omega

lemma finExpand_not_in {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (s : Finset (Fin n)) :
  v ∉ s.image (finExpand  v) := by
  intro h
  simp at h
  obtain ⟨x, hx, h_eq⟩ := h
  rw [finExpand, ← h_eq] at h_eq
  simp_all only [ge_iff_le, dite_eq_ite]
  split at h_eq
  next h =>
    split at h_eq
    next h_1 => simp_all only [lt_self_iff_false]
    next h_1 => simp_all only [lt_self_iff_false, not_false_eq_true, Fin.mk.injEq, add_right_eq_self, one_ne_zero]
  next h =>
    split at h_eq
    next h_1 =>
      simp_all only [not_lt, lt_add_iff_pos_right, zero_lt_one, Fin.mk.injEq, self_eq_add_right, one_ne_zero]
    next h_1 => simp_all only [not_lt, lt_add_iff_pos_right, zero_lt_one, not_true_eq_false]

lemma finDrop_expand_inverse_set {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (s : Finset (Fin n)) :
  Finset.image (finDrop nposi v) (Finset.image (finExpand v) s) = s := by
  -- 各要素に `finDrop` と `finExpand` を適用する
  ext x
  apply Iff.intro
  -- `x` が `s` に含まれる場合を考える
  · simp only [Finset.mem_image, exists_prop]
    rintro ⟨y, hy, hxy⟩
    -- `finDrop_expand_inverse` を適用し、元の要素が戻ることを証明
    subst hxy
    obtain ⟨w, h⟩ := hy
    obtain ⟨left, right⟩ := h
    subst right

    rw [finDrop_expand_inverse nposi v]
    exact left

  -- `x` が `s` に含まれることを仮定
  · intro hx
    rw [Finset.mem_image]
    use finExpand v x
    simp_all only [Finset.mem_image]
    apply And.intro
    · simp_all only [ge_iff_le]
      use x
    · exact finDrop_expand_inverse nposi v x

lemma finExpand_drop_inverse_set  {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (s : Finset (Fin (n+1))) (hvx: v ∉ s) :
  Finset.image (finExpand v) (Finset.image (finDrop nposi v) s) = s := by
  ext x
  apply Iff.intro
  · simp only [Finset.mem_image, exists_prop]
    intro a
    simp_all only [exists_exists_and_eq_and]
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    subst right
    have v_not_in_w : v ≠ w := by
      intro h
      subst h
      exact hvx left
    rw [finExpand_drop_inverse nposi v w v_not_in_w.symm]
    exact left
  · intro hx
    rw [Finset.mem_image]
    use finDrop nposi v x
    simp_all only [Finset.mem_image]
    apply And.intro
    · exact ⟨x, hx, rfl⟩
    · have v_neq_x : x ≠ v := by
        intro h
        subst h
        exact hvx hx
      exact finExpand_drop_inverse nposi v x v_neq_x

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

  --台集合がvを含まない場合
  lemma finDropCardEq {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (s : Finset (Fin (n+1))) (hvx: v ∉ s) :
  (Finset.image (finDrop nposi v) s).card = s.card := by
    --rw [←finExpand_drop_inverse_set nposi v s hvx]
    let ss := Finset.image (finDrop nposi v) s
    let sss:= Finset.image (finExpand v) ss
    have h1: sss = s := by
      exact finExpand_drop_inverse_set nposi v s hvx
    have h2: ss.card = sss.card := by
      dsimp [sss]
      exact (Finset.card_image_of_injective ss (finExpand_injective v)).symm
    rw [←h1]
    simp_all only [sss, ss]

lemma finDropMonotone {n : ℕ} {A B: Finset (Fin (n + 1))}(nposi: n >= 1) (v : Fin (n + 1)) : A ⊆ B → A.image (finDrop nposi v) ⊆ B.image (finDrop nposi v) :=
  by
    intro h
    simp_all only [Finset.subset_iff, Finset.mem_image, and_imp]
    intro a ha
    obtain ⟨b, hb, hab⟩ := ha
    rw [←hab]
    subst hab
    exact ⟨b, h hb, rfl⟩

lemma finExpandMonotone {n : ℕ} {A B: Finset (Fin n)} (v : Fin (n + 1)) : A ⊆ B → A.image (finExpand  v) ⊆ B.image (finExpand  v) :=
  by
    intro h
    simp_all only [Finset.subset_iff, Finset.mem_image, and_imp]
    intro a ha
    obtain ⟨b, hb, hab⟩ := ha
    rw [←hab]
    subst hab
    exact ⟨b, h hb, rfl⟩

--苦労して何日もかかったが、使ってない。
lemma imageEq {n : ℕ} {s : Finset (Fin n)} (nposi : n ≥ 1)
  (F : SetFamily (Fin (n + 1))) (v : Fin (n + 1)) :
  F.sets (s.image (finExpand  v)) ↔
    s ∈ (F.ground.powerset.filter (λ ss => v ∉ ss ∧ F.sets ss)).image (Finset.image (finDrop nposi v)) := by
  simp only [Finset.mem_image, Finset.mem_image, Finset.mem_image, Finset.mem_image]
  constructor
  -- 方向 1: F.sets (s.image (finExpand nposi v)) → s ∈ (F.ground.powerset.filter ...).image (Finset.image (finDrop nposi v))
  · intro h
    set t := s.image (finExpand  v) with t_def  -- t = s.image (finExpand nposi v)
    have t_ground : t ⊆ F.ground := by
      rw [t_def] at h
      exact F.inc_ground t h
    have ht_sets : F.sets t := h  -- t が F.sets に属している
    -- s = t.image (finDrop nposi v) を示す
    --simp_all only [Finset.mem_filter, Finset.mem_powerset]
    have ht_eq : s = t.image (finDrop nposi v) := by
      rw [Finset.image_image]
      ext x
      constructor
      -- 左から右 (x ∈ s → x ∈ t.image (finDrop nposi v))
      {
        intro hx
        simp only [Finset.mem_image, Function.comp_apply]
        -- x = finDrop nposi v (finExpand nposi v x) となることを確認
        have : x = finDrop nposi v (finExpand v x) := by rw [finDrop_expand_inverse nposi v x]
        rw [this]
        use x

      }
      -- 右から左 (x ∈ t.image (finDrop nposi v) → x ∈ s)
      {
        intro hx
        simp only [Finset.mem_image, Function.comp_apply] at hx
        -- x ∈ t.image (finDrop nposi v) ならば、ある y が存在して x = finDrop nposi v y となる
        obtain ⟨y, hy_in_t, hy_eq⟩ := hx
        -- x = finDrop nposi v y なので、finExpand nposi v x = y となる
        rw [← hy_eq]
        --rw [← finDrop_expand_inverse nposi v y]
        subst hy_eq
        rw [finDrop_expand_inverse nposi v y]
        exact hy_in_t
      }
    -- s = t.image (finDrop nposi v) が得られたので、次に s がフィルタされた集合族に属することを示す
    use t
    --rw [Finset.mem_filter]
    constructor
    -- t が F.ground の部分集合であることを示す
    {
      rw [Finset.mem_filter]
      constructor
      rw [Finset.mem_powerset]
      exact t_ground
      constructor
      -- v ∉ t であることを示す
      have hv_not_in_t : v ∉ t := finExpand_not_in nposi v s
      exact hv_not_in_t
      exact ht_sets
    }
    rw [t_def]
    ext x
    rw [Finset.mem_image]
    apply Iff.intro
    intro a
    rw [←t_def] at a
    rw [ht_eq]
    obtain ⟨w, h1,h2⟩ := a
    obtain ⟨left, right⟩ := h2
    exact Finset.mem_image_of_mem (finDrop nposi v) h1
    intro a
    --rw [ht_eq]
    --rw [t_def]
    use finExpand v x
    constructor
    exact Finset.mem_image_of_mem _ a
    exact finDrop_expand_inverse nposi v x

  -- 方向 2: s ∈ (F.ground.powerset.filter ...).image (Finset.image (finDrop nposi v)) → F.sets (s.image (finExpand nposi v))
  --下にある古いバージョンで証明されている？
  · intro h
    -- s = t.image (finDrop nposi v) を得る
    rcases h with ⟨t, ht_sets, ht_image⟩
    let _ := ht_image  --あとで影響する？
    rw [Finset.mem_filter] at ht_sets
    obtain ⟨left2, right2⟩ := ht_sets
    have hs_image_finDrop : s = t.image (finDrop nposi v) := (ht_image).symm

    -- t = s.image (finExpand nposi v) を証明する
    have ht_image_finExpand : t = s.image (finExpand  v) := by
      ext x
      --constructor
      -- t に属する要素は、s を finExpand したものの像に含まれる

      by_cases x_neq_v : x ≠ v
      constructor
      intro hx
      --simp_all only [Finset.mem_image, Function.comp_apply]
      subst ht_image
      simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, exists_exists_and_eq_and]

      use x
      constructor
      simp_all only [ge_iff_le]

      -- x neq v
      exact finExpand_drop_inverse nposi v x x_neq_v

      simp at x_neq_v
      intro a1
      --rw [Finset.mem_filter] at ht_sets
      subst ht_image
      simp_all only [Finset.mem_powerset, Finset.mem_image, exists_exists_and_eq_and]
      --obtain ⟨left, right⟩ := ht_sets
      obtain ⟨w, h⟩ := a1
      obtain ⟨left_1, _⟩ := right2
      obtain ⟨left_2, right_1⟩ := h
      subst right_1
      by_cases hh: w = v
      case pos =>
        subst hh
        simp_all only [Finset.mem_image, Function.comp_apply]
      case neg =>
        --simp_all only [Finset.mem_image, Function.comp_apply]
        rw [finExpand_drop_inverse nposi v w hh]
        exact left_2

      simp at x_neq_v
      rw [x_neq_v]
      apply Iff.intro
      intro a
      --simp_all only [Finset.mem_image, Function.comp_apply]
      --rw [←ht_image]
      subst ht_image
      simp_all only [Finset.mem_filter]

      intro a --mark 0
      rw [←ht_image] at a
      --subst ht_image

      simp_all only [Finset.mem_powerset, Finset.mem_image, exists_exists_and_eq_and]
      --obtain ⟨left, right⟩ := ht_sets
      obtain ⟨w, hh⟩ := a
      obtain ⟨left_1, _⟩ := right2
      obtain ⟨left_2, right_1⟩ := hh

      unfold finExpand at right_1
      by_cases hh: w > v
      case pos =>
        subst x_neq_v ht_image
        --rw [←ht_image] at left_2

        simp_all only [dite_eq_ite, Fin.coe_eq_castSucc, gt_iff_lt, Finset.mem_image]
        obtain ⟨w_1, hhh⟩ := left_2
        obtain ⟨_, right_2⟩ := hhh
        subst right_2
        split at right_1
        next h =>
          apply left_1
          simp_all only
          apply left_1
          simp_all only
          apply left_1
          simp_all only
          apply left_1
          simp_all only
          apply left_1
          simp_all only
          apply left_1
          simp_all only
          exact hh.not_lt h
        next h =>
          simp_all only [not_lt]
          rw [← right_1] at h
          simp_all only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero]
      case neg =>
          subst x_neq_v ht_image
          simp_all only [dite_eq_ite, Fin.coe_eq_castSucc, gt_iff_lt, Finset.mem_image]
          obtain ⟨w_1, h⟩ := left_2
          obtain ⟨_, right_2⟩ := h
          subst right_2
          split at right_1
          next h =>
            simp_all only [not_lt]
            rw [← right_1] at h
            simp_all only [lt_self_iff_false]
          rename_i h
          simp_all only [not_lt]
          rw [← right_1] at h
          simp_all only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero]

    rw [←ht_image_finExpand]
    exact right2.2

-- 定理のステートメント
theorem injective_image_injective {α β : Type} [DecidableEq α] [DecidableEq β]
  (f : α → β) (hf : Function.Injective f) :
  Function.Injective (λ (s : Finset α)=> Finset.image f s) :=
  by
     -- 関数が可逆であることを示すため、任意の集合 s, t に対して
    -- s.image f = t.image f ならば s = t であることを示す
    intro s t hs
    -- 集合の等価性を示すために ext を適用し、要素ごとの等価性を確認する
    apply Finset.ext
    intro x
    -- sとtのイメージにおける要素 x の属し方が等しいことを示す
    constructor
    -- まず、x ∈ s ならば x ∈ t を示す
    · intro hx
      -- x ∈ s ならば f x ∈ s.image f
      simp_all only
      have fxs: f x ∈ s.image f := by
        rw [Finset.mem_image]
        use x
      by_contra H
      have fxt: f x ∉ t.image f := by
        rw [Finset.mem_image]
        rw [Function.Injective] at hf
        --simp_all only [Finset.mem_image, not_true_eq_false]
        --obtain ⟨w, h⟩ := fxs
        --obtain ⟨left, right⟩ := h
        by_contra hh
        obtain ⟨w, h⟩ := hh
        obtain ⟨left, right⟩ := h
        have w_eq_x : w = x := hf right
        rw [w_eq_x] at left
        exact H left
      rw [hs] at fxs
      contradiction
    -- 次に、x ∈ t ならば x ∈ s を示す
    · intro hx
      -- x ∈ t ならば f x ∈ t.image f = s.image f だから、sにもxが存在する
      simp_all only
      have fxt: f x ∈ t.image f := by
        rw [Finset.mem_image]
        use x
      by_contra H
      have fxs: f x ∉ s.image f := by
        rw [Finset.mem_image]
        rw [Function.Injective] at hf
        by_contra hh
        obtain ⟨w, h⟩ := hh
        obtain ⟨left, right⟩ := h
        have w_eq_x : w = x := hf right
        rw [w_eq_x] at left
        exact H left
      rw [←hs] at fxt
      contradiction

lemma imageEq_card {n : ℕ} (nposi : n ≥ 1)
    (F : SetFamily (Fin (n + 1))) (v : Fin (n + 1)) :
    ((Finset.image (finDrop nposi v) F.ground).powerset.filter (λ s => F.sets (s.image (finExpand v)))).card =
      (F.ground.powerset.filter (λ ss => v ∉ ss ∧ F.sets ss)).card := by

  -- 定義域と共域のセットを明確にする
  let left_set := (Finset.image (finDrop nposi v) F.ground).powerset.filter (λ s => F.sets (s.image (finExpand v)))
  let right_set := (F.ground.powerset.filter (λ ss => v ∉ ss ∧ F.sets ss))

  -- バイジェクションを定義する
  let to_fun := λ s : Finset (Fin n) => s.image (finExpand v)
  let inv_fun := λ s : Finset (Fin (n + 1)) => s.image (finDrop nposi v)

  --have bij1 : ∀ (s : Finset (Fin n)) (hs : s ∈ left_set), Finset (Fin (n + 1)) := λ s hs => to_fun s

  -- 1. to_fun は left_set の要素を right_set の要素に写すことを証明
  have bij1_proof : ∀ s ∈ left_set, to_fun s ∈ right_set := by
    intro s hs
    -- to_fun s = s.image finExpand v
    --rw [Finset.mem_filter] at hs
    dsimp [right_set]
    rw [Finset.mem_filter]
    constructor
    -- v ∉ to_fun s の証明
    · simp_all only [Finset.mem_filter, Finset.mem_powerset, left_set, to_fun]
      obtain ⟨_, right⟩ := hs
      apply F.inc_ground
      exact right

    -- F.sets (to_fun s) の証明
    · constructor
      dsimp [to_fun]
      rw [Finset.mem_filter] at hs
      exact finExpand_not_in nposi v s
      simp_all only [Finset.mem_filter, Finset.mem_powerset, left_set, to_fun]
/-
  have bij13 : ∀ s ∈ left_set, ∃ t ∈ right_set, to_fun s = t := by
    intro s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨left, right⟩ := hs
    simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, not_exists, not_and, and_true, and_imp,
      exists_eq_right', true_and, left_set, to_fun, right_set]
    intro x a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    have : finExpand v x = finExpand v x := rfl
    simp_all only
    have : finExpand v x = finExpand v x := by rw [← a_1]
    simp_all only
    have a_2 : finExpand v x = finExpand v x := rfl
    simp_all only
    have : finExpand v x = finExpand v x := by simp
    simp_all only
    have := bij1_proof s
    simp_all only [bij1_proof]
-/
/-
  have bij1expected: (a : Finset (Fin n)) → a ∈ Finset.filter (fun s => F.sets (Finset.image (finExpand v) s))
          (Finset.image (finDrop nposi v) F.ground).powerset → Finset (Fin (n + 1)) := by
    intro a
    intro ha
    simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, not_exists, not_and, and_true, and_imp,
      left_set, to_fun, right_set, inv_fun]
    obtain ⟨left, right⟩ := ha
    simp_all only [exists_eq_right', Finset.mem_image, not_exists, not_and, and_true, true_and]
    apply to_fun
    exact a


  -- 2. inv_fun は right_set の要素を left_set の要素に写すことを証明
  have bij2 : ∀ (s : Finset (Fin (n + 1))) (hs : s ∈ right_set), Finset (Fin n) :=
  λ s hs => inv_fun s

  have bij2_proof : ∀ s ∈ right_set, inv_fun s ∈ left_set := by
    intro s hs
    dsimp [left_set]
    rw [Finset.mem_filter]
    constructor
    -- inv_fun s ⊆ Finset.image finDrop F.ground
    · simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, not_exists, not_and, and_true, and_imp,
      left_set, to_fun, right_set, inv_fun]
      obtain ⟨left, right⟩ := hs
      obtain ⟨left_1, right⟩ := right
      intro x hx
      simp_all only [Finset.mem_image]
      obtain ⟨w, h⟩ := hx
      obtain ⟨left_2, right_1⟩ := h
      subst right_1
      exact ⟨w, left left_2, rfl⟩


    -- F.sets ((inv_fun s).image finExpand v)
    · have : (s.image (finDrop nposi v)).image (finExpand v) = s := by
        rw [finExpand_drop_inverse nposi v s]
        rw [Finset.filter_eq_self (λ x => x ≠ v) hs.1]
      simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, not_exists, not_and, and_true, and_imp,
        left_set, to_fun, right_set, inv_fun]
  -/
  -- 3. to_fun ∘ inv_fun = id on right_set を証明
  /-
  have bij3 : ∀ s ∈ right_set, to_fun (inv_fun s) = s := by
    intro s hs
    rw [finExpand_drop_inverse nposi v s]
    rw [Finset.filter_eq_self (λ x => x ≠ v) hs.1]
  -/

  have bij3new : ∀ (a1), a1 ∈ left_set → ∀ (a2), a2 ∈ left_set → to_fun a1 = to_fun a2 → a1 = a2 := by
    intro a1 _
    intro ha1 _
    intro h
    exact injective_image_injective (finExpand v) (finExpand_injective v) h

  -- 4. inv_fun ∘ to_fun = id on left_set を証明。いや、全射性を示す必要がある。以下はま違い。
  /-
  have bij4 : ∀ s ∈ left_set, inv_fun (to_fun s) = s := by
    intro s hs
    dsimp [to_fun, inv_fun]
    exact finDrop_expand_inverse_set nposi v s
  -/

  have bij4new :  ∀ b ∈ Finset.filter (fun ss => v ∉ ss ∧ F.sets ss) F.ground.powerset,
    ∃ a, ∃ (_ :a ∈ Finset.filter (fun s => F.sets (Finset.image (finExpand v) s))
            (Finset.image (finDrop nposi v) F.ground).powerset),
        to_fun a = b := by
    intro b
    intro hb
    rw [Finset.mem_filter] at hb
    obtain ⟨left, right⟩ := hb
    obtain ⟨left_1, right_1⟩ := right
    use Finset.image (finDrop nposi v) b
    constructor
    simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, not_exists, not_and, and_true, and_imp,
      left_set, to_fun, right_set, inv_fun]
    rw [finExpand_drop_inverse_set nposi v b]
    exact left_1
    rw [Finset.mem_filter]
    constructor

    simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, Finset.mem_image, not_exists, not_and, and_true,
      and_imp, exists_eq_right', true_and, subset_refl, not_false_eq_true, left_set, to_fun, right_set, inv_fun]

    exact finDropMonotone nposi v left

    rw [finExpand_drop_inverse_set nposi v b]
    exact right_1

    exact left_1

  -- すべての条件を満たしているので、バイジェクションを示す

  dsimp [left_set] at bij3new
  --dsimp [left_set] at bij4
  exact Finset.card_bij (λ s _ => to_fun s) bij1_proof bij3new bij4new


def deletionToN {n : ℕ} (nposi : n ≥ 1) (F : SetFamily (Fin (n + 1))) (v : Fin (n + 1)) (_: v ∉ F.ground) (gcard: F.ground.card >= 1): SetFamily (Fin n) :=
 --エラーはDecidableを除いたら消えた。
 --hvfのかていは 必要ないのか？
 let new_ground : Finset (Fin n) := Finset.image (finDrop nposi v) F.ground
 {
  ground := new_ground,

  sets := λ s => F.sets (s.image (finExpand v : Fin n → Fin (n + 1))),

  inc_ground := λ s hs =>
  by
    simp_all only [ge_iff_le]

    have mono: s.image (finExpand v) ⊆ F.ground := by
      apply F.inc_ground
      exact hs

    have goal: s ⊆ F.ground.image (finDrop nposi v) := by
      let result := finDropMonotone nposi v mono
      rw [finDrop_expand_inverse_set nposi v] at result
      exact result

    exact goal,
  nonempty_ground := by
    simp_all only [ge_iff_le, Finset.one_le_card, Finset.image_nonempty, new_ground]
 }

def IdealFamily.deletionToN {n : ℕ} (nposi : n ≥ 1)
  (F : IdealFamily (Fin (n + 1))) (v : Fin (n + 1)) (hvf : v ∉ F.ground)
  (gcard : F.ground.card ≥ 1) : IdealFamily (Fin n) :=
let new_ground : Finset (Fin n) := Finset.image (finDrop nposi v) F.ground
{
  ground := new_ground,

  sets := λ s => F.sets (s.image (finExpand v : Fin n → Fin (n + 1))),

  inc_ground := λ s hs =>
  by
    have mono : s.image (finExpand v) ⊆ F.ground := F.inc_ground _ hs
    have goal : s ⊆ F.ground.image (finDrop nposi v) :=
    by
      let result := finDropMonotone nposi v mono
      rw [finDrop_expand_inverse_set nposi v] at result
      exact result
    exact goal,

  empty_mem := by
    -- 空集合が必ず `sets` に含まれることを示す
    simp only [Finset.image_empty]
    exact F.empty_mem,

  univ_mem := by
    -- 全体集合が `sets` に含まれることを示す
    simp only [Finset.univ]
    simp_all only [ge_iff_le, Finset.one_le_card, new_ground]
    rw [finExpand_drop_inverse_set nposi v]
    -- goal v ∉ F.ground
    -- goal F.sets F.ground
    exact F.univ_mem
    simp_all only [not_false_eq_true]
    --exacts [finDrop_mem nposi, hvf]
    --exact F.univ_mem,

  down_closed := by
    -- ダウンワード閉包性を示す
    intros A B hB hBneq hsubset
    simp_all only [ne_eq, new_ground]
    simp_all only [ge_iff_le, Finset.one_le_card]
    have lem1: B.image (finExpand v) ⊆ F.ground := by
      apply F.inc_ground
      exact hB
    have lem2: Finset.image (finDrop nposi v) (B.image (finExpand v)) ⊆ Finset.image (finDrop nposi v) F.ground := by
      apply finDropMonotone nposi v lem1
    have lem0: B ⊆ Finset.image (finDrop nposi v) F.ground := by
      rw [finDrop_expand_inverse_set nposi v] at lem2
      exact lem2
    have lem3: B ⊂ Finset.image (finDrop nposi v) F.ground := by
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨lem0, hBneq⟩
    have lemz {C D:Finset α }: C ⊂ D → ∃ y, y ∈ D ∧ y ∉ C := by
      intro h
      have h_exists := Finset.exists_of_ssubset h
      simp_all only
    have lem4: ∃ (y: Fin n), y ∈ Finset.image (finDrop nposi v) F.ground ∧ y ∉ B := by
      --simp_all only [Finset.mem_image, exists_exists_and_eq_and]
      --rw [Finset.ssubset_iff_subset_ne] at lem3
      have h_exists := Finset.exists_of_ssubset lem3
      simp_all only

    have h_inc: A.image (finExpand v) ⊆ B.image (finExpand v) := by
      apply finExpandMonotone v
      exact hsubset
    have hBneq2: (B.image (finExpand v)) ≠ F.ground := by
      intro h
      apply hvf
      rw [←h]
      simp_all only
      obtain ⟨y, hy, hyneq⟩ := lem4
      simp_all only [subset_refl, Finset.mem_image]
      obtain ⟨w, h_1⟩ := hy
      obtain ⟨left, right⟩ := h_1
      --subst right
      have hwg: w ∈ F.ground := by
        subst right
        simp_all only [not_true_eq_false]
      have hw: w ∉ B.image (finExpand v) := by
        intro _
        subst right
        simp_all only [not_false_eq_true]
        have lem5: finDrop nposi v w ∈ Finset.image (finDrop nposi v) (B.image (finExpand v)) := by
          simp_all only [Finset.mem_image]
          use w
        rw [finDrop_expand_inverse_set nposi v] at lem5
        simp_all only [not_true_eq_false]
        --w in B.image (finExpand v)とfinDrop nposi v w ∉ Bが矛盾するはず。

      apply hvf
      rw [←h]
      simp_all only

    have hB' := F.down_closed (A.image (finExpand v)) (B.image (finExpand v)) hB hBneq2 (finExpandMonotone v hsubset)

    --simp only [Finset.image_subset] at hsubset

    exact hB'

  nonempty_ground := by
    simp_all only [ge_iff_le, Finset.one_le_card, Finset.image_nonempty, new_ground]
}

lemma IdealFamily.deletionToN_number {n : ℕ} (nposi : n ≥ 1)
  (F : IdealFamily (Fin (n + 1))) (v : Fin (n + 1)) (hvf : v ∉ F.ground)
  (gcard : F.ground.card ≥ 1) : number_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi F v hvf gcard).toSetFamily = number_of_hyperedges F.toSetFamily := by
  rw [number_of_hyperedges]
  simp_all only [IdealFamily.deletionToN]
  rw [number_of_hyperedges]
  --have nnposi: n + 1 ≥ 1 := by omega

  apply Eq.symm
  --以下はコメントアウトするとなぜかエラーが出る。
  have eqlem: (Finset.filter (λ s => F.sets (Finset.image (finExpand v) s)) (Finset.image (finDrop nposi v) F.ground).powerset).card = (Finset.filter (λ s => v ∉ s ∧ F.sets s) F.ground.powerset).card := by
    exact imageEq_card nposi F.toSetFamily v

  simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
  simp_all only [ge_iff_le, Finset.one_le_card]
  congr 1
  ext1 a
  simp_all only [Finset.mem_filter, Finset.mem_powerset, and_congr_right_iff, iff_and_self]
  intro a_1 _
  apply Aesop.BuiltinRules.not_intro
  intro a_3
  exact hvf (a_1 a_3)

-- 仮定として、IdealFamilyが定義されているとします。
-- 必要に応じて、適切なインポートや定義を追加してください。

variable {n : ℕ}
variable (F : IdealFamily (Fin (n+1)))
variable (nposi : n ≥ 1)
variable (v : Fin (n+1))
variable (hvf : v ∉ F.ground)
variable (gcard : F.ground.card ≥ 1)

-- finDrop は v を含まない部分集合に対して単射である
lemma finDrop_injective_except_v : ∀ s : Finset (Fin (n+1)), v ∉ s → Function.Injective (finDrop nposi v) :=
by
  -- 証明： finDrop が単射であることを示すが、v を含まない部分集合に限定
  intros a b h hva hvb
  by_cases h₁ : a < v
  case pos =>
    -- a < v の場合、 finDrop は恒等写像なので、 a = b である必要がある
    rw [Fin.val_lt, h] at h₁
    exact Fin.eq_of_veq h₁
  case neg =>
    -- a ≥ v の場合、 finDrop は a と b を -1 したもので比較するので、同様に a = b でなければならない
    rw [Fin.val_ge, h] at h₁
    exact Fin.eq_of_veq h₁

-- 証明の主定理
theorem sum_card_eq_sum_card :
  (F.ground.powerset.filter F.sets).sum Finset.card =
    (Finset.image (finDrop nposi v) F.ground).powerset.filter (fun s => F.sets (Finset.image (finExpand v) s)).sum Finset.card :=
by
  -- 定義するフィンスセットの集合
  let s_fin := F.ground.powerset.filter F.sets
  let t_fin := (Finset.image (finDrop nposi v) F.ground).powerset.filter (λ s, F.sets (Finset.image (finExpand v) s))

  -- v を含まない集合に限定して finDrop が単射であることを利用する
  have h1 : ∀ s ∈ s_fin, v ∉ s → Finset.image (finDrop nposi v) s ∈ t_fin :=
    by
      intros s hs hvs
      split
      -- finDrop '' s ⊆ finDrop(F.ground) を示す
      exact Finset.image_subset _ hs.1
      -- F.sets (Finset.image finExpand v (finDrop '' s)) = F.sets s を示す
      rw [finExpand_drop_inverse_set nposi v s hvs]
      exact hs.2

  -- finDrop が v を含まない部分集合に対して単射であることを示す
  have h2 : ∀ s t ∈ s_fin, v ∉ s → v ∉ t → Finset.image (finDrop nposi v) s = Finset.image (finDrop nposi v) t → s = t :=
    by
      intros s t hs ht hvs hvt h
      -- finDrop が単射である部分集合での証明
      apply Finset.ext
      intro x
      split
      -- s ⊆ t を示す
      intros hx
      rw [Finset.mem_image] at hx
      cases hx with y hy
      rw [← hy.2] at h
      rw [Finset.mem_image] at h
      cases h with z hz
      rw [hz.2] at hy
      exact Finset.mem_of_mem_filter_left hy.1
      -- t ⊆ s を示す
      intros hx
      rw [Finset.mem_image] at hx
      cases hx with y hy
      rw [← hy.2] at h
      rw [Finset.mem_image] at h
      cases h with z hz
      rw [hz.2] at hy
      exact Finset.mem_of_mem_filter_left hy.1

  -- finExpand が surjective であることを示す
  have h3 : ∀ t ∈ t_fin, ∃ s ∈ s_fin, v ∉ s ∧ Finset.image (finDrop nposi v) s = t :=
    by
      intros t ht
      -- s = finExpand '' t として、 s が存在することを示す
      use Finset.image (finExpand v) t
      split
      -- s ∈ s_fin を示す
      split
      -- finExpand '' t ⊆ F.ground を示す
      exact Finset.image_subset (finDrop nposi v) F.set_subset_ground
      -- F.sets (Finset.image finExpand v (finDrop '' (finExpand '' t))) = F.sets (finExpand '' t) を示す
      rw [finExpand_drop_inverse_set nposi v t (Finset.not_mem_image_of_mem (fun x => Finset.mem_of_mem_powerset ht.1))]
      exact ht.2

  -- 重み関数が一致することを示す
  have h4 : ∀ s ∈ s_fin, v ∉ s → Finset.card s = Finset.card (Finset.image (finDrop nposi v) s) :=
    by
      intros s hs hvs
      -- finDrop が injective であるため、Finset.card s = Finset.card (finDrop '' s)
      exact Finset.card_image_of_injective s (finDrop_injective_except_v s hvs)

  -- これらの補題を基にして、Finset.sum_bij を適用
  apply Finset.sum_bij (λ s : Finset (Fin (n+1)), Finset.image (finDrop nposi v) s)
  exact h1
  exact h2
  exact h3
  exact h4

lemma finDrop_injective {n : ℕ} (nposi : n ≥ 1) (v : Fin (n+1)) :
  Function.Injective (finDrop nposi v) :=
by
  intros a b h
  unfold finDrop at h
  split_ifs at h with h1 h2
  -- どちらも a.val と b.val が v.val 未満のケース
  case h1 h2 => exact Fin.eq_of_veq h
  -- どちらも a.val と b.val が v.val 以上のケース
  case neg neg => exact Fin.eq_of_veq (nat.succ_injective h)
  -- 一方が v.val 未満、もう一方が v.val 以上の場合
  case h1 neg => exfalso; apply nat.lt_asymm h1 h
  case neg h2 => exfalso; apply nat.lt_asymm h2 h

theorem sum_card_eq_sum_card :
  (F.ground.powerset.filter F.sets).sum Finset.card =
    (Finset.image (finDrop nposi v) F.ground).powerset.filter (fun s => F.sets (Finset.image (finExpand v) s)).sum Finset.card :=
by
  -- 定義するフィンスセットの集合
  let s_fin := F.ground.powerset.filter F.sets
  let t_fin := (Finset.image (finDrop nposi v) F.ground).powerset.filter (λ s, F.sets (Finset.image (finExpand v) s))

  -- Injectivity の証明
  have h_injective : ∀ s ∈ s_fin, v ∉ s → Finset.image (finDrop nposi v) s ∈ t_fin :=
    by
      intros s hs hvs
      split
      -- finDrop '' s ⊆ finDrop(F.ground) を示す
      exact Finset.image_subset _ hs.1
      -- F.sets (Finset.image finExpand v (finDrop '' s)) = F.sets s を示す
      rw [finExpand_drop_inverse_set nposi v s hvs]
      exact hs.2

  -- Surjectivity の証明
  have h_surjective : ∀ t ∈ t_fin, ∃ s ∈ s_fin, v ∉ s ∧ Finset.image (finDrop nposi v) s = t :=
    by
      intros t ht
      -- s = finExpand '' t として、 s が存在することを示す
      use Finset.image (finExpand v) t
      split
      -- s ∈ s_fin を示す
      split
      -- finExpand '' t ⊆ F.ground を示す
      exact Finset.image_subset (finDrop nposi v) F.set_subset_ground
      -- F.sets (Finset.image finExpand v (finDrop '' (finExpand '' t))) = F.sets (finExpand '' t) を示す
      rw [finExpand_drop_inverse_set nposi v t (Finset.not_mem_image_of_mem (fun x => Finset.mem_of_mem_powerset ht.1))]
      exact ht.2

  -- Finset.sum_bij の適用
  apply Finset.sum_bij
  -- bijective 関係の定義
  exact h_injective
  -- 単射性
  exact fun s t hs ht hvs hvt h => Finset.ext fun x => ⟨Finset.mem_of_mem_image_left, Finset.mem_of_mem_image_right⟩
  -- 全射性
  exact h_surjective
  -- 重み関数の一致
  intros s hs hvs
  exact Finset.card_image_of_injective s (finDrop_injective_except_v s hvs)

lemma IdealFamily.deletionToN_total {n : ℕ} (nposi : n ≥ 1)
  (F : IdealFamily (Fin (n + 1))) (v : Fin (n + 1)) (hvf : v ∉ F.ground)
  (gcard : F.ground.card ≥ 1) : total_size_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi F v hvf gcard).toSetFamily = total_size_of_hyperedges F.toSetFamily := by
  rw [total_size_of_hyperedges]
  simp_all only [IdealFamily.deletionToN]
  rw [total_size_of_hyperedges]
  simp
  apply Eq.symm
  have : (Finset.filter F.sets F.ground.powerset) =
         (Finset.filter (fun s => F.sets (Finset.image (finExpand v) s))
                        (Finset.image (finDrop nposi v) F.ground).powerset) := by


  #check Finset.sum_congr
  apply Finset.sum_congr
  -- まず、集合の等式を示す。
  -- finDrop と finExpand が互いに逆写像であることから、フィルター条件が一致する。
  {
    -- ゴールのセットが同一であることを示す
    have : Finset.image (finDrop nposi v) (Finset.image (finExpand v) F.ground.powerset) = F.ground.powerset := by
      exact finDrop_expand_inverse_set nposi v F.ground.powerset
    rw [this]
    simp



  }
  -- 各集合のカーディナリティが等しいことを示す。
  {
    intros s hs
    -- s の各カードが同一であることは Finset.card に依存するため、すべてのフィルタリング後のカードは同じ。
    search_proof
  }






def P (x:Nat) : Prop := x ≥ 2  ∧ ∀ (F: IdealFamily (Fin x)), F.ground.card = x → normalized_degree_sum F.toSetFamily ≤ 0


theorem induction_step {n:Nat} (hn: n >= 2) (h: P n) : P (n+1) := by
  -- ここでFintypeインスタンスを明示的に使用
  --have fintype_ground : Fintype F.ground := finF
  have nposi : n ≥ 1 := by omega
  unfold P at h ⊢
  obtain ⟨h_ge2, h_ind⟩ := h

  constructor
  simp_all only [ge_iff_le, Nat.reduceLeDiff]
  --obtain ⟨left, right⟩ := h
  --omega
  intros F hcard
   -- n ≥ 2 から n + 1 ≥ 3 を導く
  have hcard0: F.ground.card >= 2 := by
    have h1 : n + 1 ≥ 3 := Nat.succ_le_succ hn
    -- F.ground.card = n + 1 なので、F.ground.card ≥ 3
    rw [←hcard] at h1
    -- F.ground.card ≥ 3 なので F.ground.card ≥ 2 も成立
    exact Nat.le_of_succ_le h1

  obtain ⟨v, hv⟩ := ideal_version_of_frankl_conjecture F
    --#check hv
  obtain ⟨hv_left, hv_right⟩ := hv

  by_cases hv_singleton: F.sets {v}
  case pos =>

  classical
  by_cases hv_hyperedge:(F.sets (F.ground \ {v}))
  case pos =>
    have h_sum_have := (hyperedge_average_have F v hv_left hcard0) hv_hyperedge
    --have h_idealdeletion := (IdealDeletion.idealdeletion F v hv_left hcard0)
    set Fdel := IdealDeletion.idealdeletion F v hv_left hcard0
    have Fvx: v ∉ Fdel.ground := by
      intro h
      simp_all only [ge_iff_le]
      dsimp [Fdel] at h
      simp_all only [Fdel]
      dsimp [IdealDeletion.idealdeletion] at h
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true]

    have hcard1: Fdel.ground.card = n := by
      simp_all only [ge_iff_le]
      simp_all only [Fdel]
      rw [IdealDeletion.idealdeletion]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]

    have hcard2: Fdel.ground.card ≥ 1 := by
      simp_all only [ge_iff_le]

    #check IdealFamily.deletionToN nposi Fdel v Fvx hcard2
    set h_idealdeletion := IdealFamily.deletionToN nposi Fdel v Fvx hcard2
    --IdealFamily (Fin (n + 1))になっているがFin nになってほしい。

    have hcard3: h_idealdeletion.ground.card = n := by
      dsimp [h_idealdeletion]
      dsimp [IdealFamily.deletionToN]
      --rw [Finset.card_image_of_injective]
      rw  [finDropCardEq nposi v Fdel.ground Fvx]
      exact hcard1

    set Fcont :=  (IdealDeletion.contraction_ideal_family F v hv_singleton hcard0)
    have h_cont: Fcont.ground.card = n := by
      simp_all only [ge_iff_le]
      simp_all only [IdealDeletion.contraction]
      rename_i hcard1_1 h_ind_2 h_sum_have_2
      simp_all only [ge_iff_le, implies_true, sub_left_inj, add_left_inj, add_right_inj, Fdel, Fcont]
      rw [IdealDeletion.contraction_ideal_family]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]
      rw [IdealDeletion.contraction]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]

    have h_cont2: Fcont.ground.card ≥ 1 := by
      simp_all only [ge_iff_le]

    have Fvx2: v ∉ Fcont.ground := by
      intro h
      simp_all only [ge_iff_le]
      dsimp [Fcont] at h
      simp_all only [Fcont]
      dsimp [IdealDeletion.contraction_ideal_family] at h
      dsimp [IdealDeletion.contraction] at h
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true]

    have h_cont_card: Fcont.ground.card = n := by
      simp_all only [ge_iff_le]

    set h_contraction := IdealFamily.deletionToN nposi Fcont v Fvx2 h_cont2
    have h_cont_card2: h_contraction.ground.card = n := by
      simp_all only [ge_iff_le]
      dsimp [h_contraction]
      dsimp [IdealFamily.deletionToN]
      rw [finDropCardEq nposi v Fcont.ground Fvx2]
      exact h_cont_card

    rw [h_sum_have]
    dsimp [Fdel] at hcard1
    #check (h_ind h_idealdeletion) hcard3
    let h_idealdeletion2 := h_ind h_idealdeletion hcard3
    #check h_ind h_contraction
    let h_contraction2 := (h_ind h_contraction) h_cont_card2

    let sum_have := hyperedge_average_have F v hv_left hcard0 hv_hyperedge
    let number_have :=  hyperedge_count_deletion_contraction_have_z F v hv_left hcard0 hv_hyperedge

    simp only [ge_iff_le, tsub_le_iff_right, zero_add, Fdel, Fcont] at h_idealdeletion2 h_contraction2 sum_have number_have  ⊢
    simp only [normalized_degree_sum, IdealFamily.toSetFamily] at h_idealdeletion2 h_contraction2 sum_have number_have ⊢
    --simp only [IdealFamily.deletionToN] at h_idealdeletion2 h_contraction2 sum_have number_have  ⊢

    rw [IdealFamily.deletionToN_number nposi Fdel v Fvx hcard2] at h_idealdeletion2
    rw [IdealFamily.deletionToN_number nposi Fcont v Fvx2 h_cont2] at h_contraction2
    --上はIdealFamily.deletionToNしても、hyperedgeの数がかわらないこと
    --numberの方は上で置き換わったが、sumの方は置き換わっていない。
    --ground setの大きさもdeletionToNで変わらないことを示す必要がある。

    --今になって考えてみれば、Fin nを使わずにground setの大きさで議論する方法の方が良かった。

    --let total_del := (total_size_of_hyperedges ((@IdealFamily.deletionToN (Fin n) n nposi Fdel v Fvx hcard2):IdealFamily (Fin n)).1)
    set total_del := total_size_of_hyperedges (IdealDeletion.idealdeletion F v hv_left hcard0).1 with h_total_del
    --set number_del := (number_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi Fdel v Fvx hcard2).1) with number_del
    set number_del := (number_of_hyperedges (IdealDeletion.idealdeletion F v hv_left hcard0).1) with h_number_del
    --let total_cont := (total_size_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi Fcont v Fvx2 h_cont2).1)
    set total_cont := total_size_of_hyperedges (IdealDeletion.contraction F.1 v hv_left hcard0) with h_total_cont
    --let number_cont := (number_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi Fcont v Fvx2 h_cont2).1)
    set number_cont := (number_of_hyperedges (IdealDeletion.contraction F.1 v hv_left hcard0)) with h_number_cont
    let total := (total_size_of_hyperedges F.toSetFamily)
    let number := (number_of_hyperedges F.toSetFamily)
    let degreev := (degree F.toSetFamily v)

    rw  [←h_total_del] at *
    rw [←h_number_del] at *
    rw [←h_total_cont] at *
    rw [←h_number_cont] at *
    rw [hcard1] at *
    --#check h_cont_card
    dsimp [Fcont] at h_cont_card
    dsimp [IdealDeletion.contraction_ideal_family] at h_cont_card
    rw [h_cont_card] at *
    --rw [←total]
    --subst number
    --subst degreev
    --rw [h_idealdeletion2, h_contraction2, sum_have, number_have]
    linarith
    --linarith --[h_idealdeletion2, h_contraction2, hv_right,sum_have,number_have]
  case neg =>
    sorry

/-
--以下はChatGPTが生成した台集合の大きさに関する帰納法のテンプレート。
-- 台集合の大きさが 2 以上の場合の帰納法。上がうまくいけばこちらは消す。
theorem set_family_induction_card {X : Finset α} (P : Finset α → Prop)
  (h_base : ∀ a b : α, a ≠ b → P ({a, b}))  -- Base case: |X| = 2 の場合
  (h_inductive : ∀ (a : α) (S : Finset α), a ∉ S → P S → P (insert a S)) :
  X.card ≥ 2 → P X :=
by
  induction X.card with
  | zero =>
    -- |X| = 0 の場合: このケースは X.card ≥ 2 の仮定に反するので証明不要
    intro h_card
    linarith  -- 矛盾: |X| が 0 のとき |X| ≥ 2 は成立しない
  | succ n ih =>
    cases n with
    | zero =>
      -- |X| = 1 の場合: これは X.card ≥ 2 に反するので除外
      intro h_card
      linarith  -- 矛盾: |X| が 1 のとき |X| ≥ 2 は成立しない
    | succ m =>
      -- |X| = m + 2 の場合: これが実際に証明すべきケース
      intro h_card
      -- S は X から任意の要素 x を取り除いた集合
      --obtain ⟨x, S, hx, hXS⟩ := Finset.card_succ_iff.mp h_card
      have hS_card : S.card = m + 1 := by
        rw [hXS]
        exact Finset.card_erase_of_mem hx
      -- 帰納法の仮定を S に適用 (S の要素数は m + 1 ≥ 2 である)
      apply h_inductive x S hx
      apply ih m _  -- 帰納仮定を使って S に対して命題 P(S) を証明
      linarith  -- S の要素数 m + 1 が 2 以上であることを確認

-- 台集合の大きさが 2 以上の場合の帰納法。集合そのものでstrongInductionを使うバージョン。消して良い。
theorem set_family_induction_large {X : Finset α} (P : Finset α → Prop)
  (h_base : ∀ a b : α, a ≠ b → P ({a, b}))  -- Base case: |X| = 2 の場合
  (h_inductive : ∀ (a : α) (S : Finset α), a ∉ S → S.card ≥ 2 → P S → P (insert a S)) :
  X.card ≥ 2 → P X :=
by
  intro h_size  -- 仮定: |X| ≥ 2
  induction X using Finset.strongInduction with
  | empty =>
    -- |X| = 0 の場合はここに来ない（h_sizeにより除外される）
    cases h_size
  | insert x S h_ind ih =>
    have hS : |S| ≥ 1 := by linarith  -- Sの要素数に関する仮定
    cases Nat.eq_or_lt_of_le hS with
    | eq =>
      -- Base case: |S| = 1 の場合（つまり |X| = 2 の場合）
      cases S with
      | cons a t hat =>
        rw [Finset.insert_eq_of_mem hat]
        apply h_base x a
        intro h_eq
        -- S の要素が異なることを示すための証明
        -- 省略: x ≠ a の証明
    | lt =>
      -- Inductive step: |S| ≥ 2 の場合
      apply h_inductive x S
      exact h_ind
      linarith  -- Sの要素数の仮定から |S| ≥ 2 を導出
      apply ih hS  -- 帰納法の仮定を適用


-- Theorem: For IdealFamily with ground set of size n, the normalized degree sum is non-positive.
theorem normalized_degree_sum_non_positive (F : IdealFamily α) :
  F.ground.card >= 2 → normalized_degree_sum F.toSetFamily ≤ 0 :=
by-- Induction on the size of the ground set
  intros h_card_pos
  match F.ground.card with
  | 0 =>
    -- Base case: ground set is empty, contradiction because ground is nonempty
    sorry
  | k + 1 => --帰納法の仮定がどこに入っている？
    rename_i h_card into h_card_pos
      -- Inductive step: ground set has n + 1 elements
    -- Obtain the element v guaranteed by ideal_version_of_frankl_conjecture
    obtain ⟨v, hv⟩ := ideal_version_of_frankl_conjecture F
    --#check hv
    obtain ⟨hv_left, hv_right⟩ := hv

      -- Case 1: G \ {v} is a hyperedge
    classical
    by_cases hv_hyperedge:(F.sets (F.ground \ {v})) --with hv_hyperedge
    case pos =>
        -- Apply the hyperedge_average_have lemma
        have h_sum_have := (hyperedge_average_have F v hv_left h_card_pos) hv_hyperedge
        #check h_sum_have
        -- Use the inductive hypothesis on idealdeletion and contraction
        have h_idealdeletion :=  (IdealDeletion.idealdeletion F v hv_left h_card_pos)
        have h_contraction :=  (IdealDeletion.contraction F.toSetFamily v hv_left h_card_pos)
        --これらが非正であるという帰納法の仮定を使う。今は不等号になっていない。どうやって使うか？

        -- Since degree satisfies 2 * degree F v ≤ number_of_hyperedges F (Frankl's conjecture),
        -- we conclude normalized_degree_sum F ≤ 0
        rw [h_sum_have]
        linarith [h_idealdeletion, h_contraction, hv_right]

    -- Case 2: G \ {v} is not a hyperedge
      case neg =>
      -- Apply the hyperedge_average_none lemma
        have h_sum_none := hyperedge_average_none F v hv.1 h_card_pos hv_hyperedge
      -- Use the inductive hypothesis on idealdeletion and contraction
        have h_idealdeletion := ih (IdealDeletion.idealdeletion F v hv.1 h_card_pos)
        have h_contraction := ih (IdealDeletion.contraction F.toSetFamily v hv.1 h_card_pos)

        -- From the sum equation and the inductive hypothesis, we conclude normalized_degree_sum F ≤ 0
        rw [h_sum_none]
        linarith [h_idealdeletion, h_contraction, hv]
-/
end Ideal
