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
import Ideal.IdealSimple
import Ideal.IdealDegreeOne
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
     -- 関数が可逆であることを示すため、任意の集合 s, t に対してs.image f = t.image f ならば s = t であることを示す
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


  have bij3new : ∀ (a1), a1 ∈ left_set → ∀ (a2), a2 ∈ left_set → to_fun a1 = to_fun a2 → a1 = a2 := by
    intro a1 _
    intro ha1 _
    intro h
    exact injective_image_injective (finExpand v) (finExpand_injective v) h

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


--こっちはidealFamilyからidealFamilyへの写像
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

theorem sum_card_eq_sum_card  {n : ℕ} (F : IdealFamily (Fin (n+1))) (nposi : n ≥ 1)(v : Fin (n+1)) (hvf : v ∉ F.ground) (gcard : F.ground.card ≥ 1):
  (F.ground.powerset.filter F.sets).sum Finset.card =
    ((Finset.image (finDrop nposi v) F.ground).powerset.filter (fun s => F.sets (Finset.image (finExpand v) s))).sum Finset.card :=
by
  let s_fin := F.ground.powerset.filter F.sets
  let t_fin := (Finset.image (finDrop nposi v) F.ground).powerset.filter (λ s=> F.sets (Finset.image (finExpand v) s))

  -- 1. 対応関係 i の定義
  let i := λ (s : Finset (Fin (n+1))) (_ : s ∈ s_fin)=> Finset.image (finDrop nposi v) s

  -- 2. 対応関係 i が t_fin に含まれることを証明
  have hi : ∀ (s : Finset (Fin (n+1))) (hs : s ∈ s_fin), i s hs ∈ t_fin :=
    by
      intros s hs
      dsimp [t_fin]
      rw [Finset.mem_filter]
      constructor
      -- Finset.image (finDrop nposi v) s が t_fin に含まれることを示す
      simp_all only [Finset.mem_powerset, i, s_fin]
      simp_all only [Finset.mem_filter, Finset.mem_powerset, s_fin]
      obtain ⟨left, _⟩ := hs
      intro x hx
      simp_all only [Finset.mem_image]
      obtain ⟨w, h⟩ := hx
      obtain ⟨left_1, right_1⟩ := h
      subst right_1
      exact ⟨w, left left_1, rfl⟩

      -- F.sets (Finset.image finExpand v (Finset.image (finDrop nposi v) s)) = F.sets s を示す
      dsimp [s_fin] at hs
      rw [Finset.mem_filter] at hs
      simp_all only [Finset.mem_powerset]
      dsimp [i]
      have v_notin_s : v ∉ s := by
        apply Aesop.BuiltinRules.not_intro
        intro a
        have : v ∈ F.ground := by
           exact hs.1 a
        exact hvf this

      rw [finExpand_drop_inverse_set nposi v s v_notin_s]
      exact hs.2

  -- Injectivity の証明　内容が単射性の証明になっていない。消す。
  have h_injective_old : ∀ s ∈ s_fin, v ∉ s → Finset.image (finDrop nposi v) s ∈ t_fin :=
    by
      intros s hs hvs
      dsimp [t_fin]
      rw [Finset.mem_filter]
      constructor
      -- finDrop '' s ⊆ finDrop(F.ground) を示す
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_powerset] at hs
      simp_all only [Finset.mem_powerset]
      obtain ⟨left, _⟩ := hs
      intro x hx
      simp_all only [Finset.mem_image]
      obtain ⟨w, h⟩ := hx
      obtain ⟨left_1, right_1⟩ := h
      subst right_1
      exact ⟨w, left left_1, rfl⟩
      -- F.sets (Finset.image finExpand v (finDrop '' s)) = F.sets s を示す
      rw [finExpand_drop_inverse_set nposi v s hvs]
      dsimp [s_fin] at hs
      rw [Finset.mem_filter] at hs
      exact hs.2

  have h_injective: ∀ (a₁ : Finset (Fin (n + 1))) (ha₁ : a₁ ∈ s_fin) (a₂ : Finset (Fin (n + 1))) (ha₂ : a₂ ∈ s_fin),
  i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ :=
    by
      intros a₁ ha₁ a₂ ha₂ h
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, s_fin]
      dsimp [i] at h
      simp_all only [ge_iff_le, Finset.one_le_card, Finset.mem_filter, Finset.mem_powerset, and_imp, and_self, implies_true,
      s_fin, i, t_fin]
      obtain ⟨left, _⟩ := ha₁
      obtain ⟨left_1, _⟩ := ha₂

      have v_notin_a₁ : v ∉ a₁ := by
        intro h₁
        have : v ∈ F.ground := Finset.mem_of_subset left h₁
        exact hvf this

      have v_notin_a₂ : v ∉ a₂ := by
        intro h₂
        have : v ∈ F.ground := Finset.mem_of_subset left_1 h₂
        exact hvf this

      -- 仮定 h : Finset.image (finDrop nposi v) a₁ = Finset.image (finDrop nposi v) a₂ を利用
      have h_expand : Finset.image (finExpand v) (Finset.image (finDrop nposi v) a₁) =
                Finset.image (finExpand v) (Finset.image (finDrop nposi v) a₂) := by
         rw [h]

      -- finExpand_drop_inverse_set を適用して、元の集合が再現されることを示す
      rw [finExpand_drop_inverse_set nposi v a₁ v_notin_a₁] at h_expand
      rw [finExpand_drop_inverse_set nposi v a₂ v_notin_a₂] at h_expand

      -- よって、a₁ = a₂ が成立
      exact h_expand

  -- Surjectivity の証明の前のバージョン。消す。
  have h_surjective_org : ∀ t ∈ t_fin, ∃ s ∈ s_fin, v ∉ s ∧ Finset.image (finDrop nposi v) s = t :=
    by
      intros t ht
      -- s = finExpand '' t として、 s が存在することを示す
      use Finset.image (finExpand v) t
      constructor
      -- s ∈ s_fin を示す
      dsimp [s_fin]
      rw [Finset.mem_filter]
      constructor
      -- finExpand '' t ⊆ F.ground を示す
      dsimp [t_fin] at ht
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, s_fin, t_fin]
      obtain ⟨_, right⟩ := ht
      exact F.inc_ground (Finset.image (finExpand v) t) right

      --goal F.sets (Finset.image (finExpand v) t)
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, s_fin, t_fin]
      -- F.sets (Finset.image finExpand v (finDrop '' (finExpand '' t))) = F.sets (finExpand '' t) を示す
      simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_image, not_exists, not_and, s_fin,
        t_fin]
      --obtain ⟨left, right⟩ := ht
      apply And.intro
      · intro x _
        apply Aesop.BuiltinRules.not_intro
        intro a_1
        --lemma finExpand_not_in {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (s : Finset (Fin n)):v ∉ s.image (finExpand  v)
        apply finExpand_not_in nposi v {x}
        simp_all only [Finset.mem_image]
        use x
        constructor
        simp_all only [Finset.mem_singleton]
        exact a_1

      · exact finDrop_expand_inverse_set  nposi  v t

  have h_surjective :  ∀ b ∈ Finset.filter (fun s => F.sets (Finset.image (finExpand v) s)) (Finset.image (finDrop nposi v) F.ground).powerset,
    ∃ a, ∃ (ha : a ∈ s_fin), i a ha = b := by
    intro b
    intro hb
    rw [Finset.mem_filter] at hb
    obtain ⟨left, right⟩ := hb
    dsimp [s_fin]
    dsimp [i]
    have nnposi: n + 1 ≥ 1 := by omega
    --use Finset.image (finDrop nnposi v) b
    use Finset.image (finExpand v) b
    constructor
    exact finDrop_expand_inverse_set nposi v b
    rw [Finset.mem_filter]
    constructor
    swap
    exact right
    simp_all only [Finset.mem_powerset, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, not_exists, not_and, and_true, and_imp,
      exists_eq_right', true_and, s_fin, i, t_fin]
    exact F.inc_ground (Finset.image (finExpand v) b) right

  have h_com: ∀ (a : Finset (Fin (n + 1))) (ha : a ∈ s_fin), a.card = (i a ha).card :=
    by
      intros s hs
      simp_all only [s_fin, i]
      have v_notin_s : v ∉ s := by
        intro h
        dsimp [s_fin] at hs
        rw [Finset.mem_filter] at hs
        simp only [Finset.mem_powerset] at hs
        exact hvf (hs.1 h)
      exact (finDropCardEq nposi v s v_notin_s).symm
      --goal s.card = (Finset.image (finDrop nposi v) s).card

  -- Finset.sum_bij の適用
  apply Finset.sum_bij
  -- bijective 関係の定義
    fun s => i s
    --
  exact hi
  exact h_injective

  exact h_surjective
    -- 重み関数の一致
  --goal ∀ (a : Finset (Fin (n + 1))) (ha : a ∈ s_fin), a.card = (i a ha).card
  exact h_com

lemma deletion_total: ∀ (n : ℕ) (F : IdealFamily (Fin (n + 1))) (nposi : n ≥ 1) (v : Fin (n + 1)) (hvf : v ∉ F.ground) (gcard : F.ground.card ≥ 1),
  total_size_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi F v hvf gcard).toSetFamily = total_size_of_hyperedges F.toSetFamily :=
  by
    intros n F nposi v hvf gcard
    simp only [total_size_of_hyperedges]
    simp only [IdealFamily.deletionToN]
    have h2 := sum_card_eq_sum_card F nposi v hvf gcard
    rw [h2]

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
  · case pos =>

    set Fdel := IdealDeletion.idealdeletion F v hv_left hcard0
    have Fvx: v ∉ Fdel.ground := by
      intro h
      simp_all only [ge_iff_le]
      dsimp [Fdel] at h
      --simp_all only [Fdel]
      dsimp [IdealDeletion.idealdeletion] at h
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true]

    have hcard1: Fdel.ground.card = n := by
      simp_all only [ge_iff_le]
      simp_all only [Fdel]
      rw [IdealDeletion.idealdeletion]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]

    have hcard2: Fdel.ground.card ≥ 1 := by
      simp_all only [ge_iff_le]

    --#check IdealFamily.deletionToN nposi Fdel v Fvx hcard2
    set h_idealdeletion := IdealFamily.deletionToN nposi Fdel v Fvx hcard2
    --IdealFamily (Fin (n + 1))になっているがFin nになってほしい。

    have hcard3: h_idealdeletion.ground.card = n := by
      dsimp [h_idealdeletion]
      dsimp [IdealFamily.deletionToN]
      rw  [finDropCardEq nposi v Fdel.ground Fvx]
      exact hcard1

    have h_del_card: (@IdealFamily.deletionToN (Fin n) n nposi (IdealDeletion.idealdeletion F v hv_left hcard0) v Fvx
                hcard2).ground.card = n := by
      simp_all only [ge_iff_le]
      simp_all only [ge_iff_le, implies_true, imp_self, forall_true_left, Fdel, h_idealdeletion]
      exact hcard3

    set Fcont :=  (IdealDeletion.contraction_ideal_family F v hv_singleton hcard0)
    have h_cont: Fcont.ground.card = n := by
      simp_all only [ge_iff_le]
      --simp_all only [IdealDeletion.contraction]
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

    have h_cont_card2: (IdealDeletion.contraction_ideal_family F v hv_singleton hcard0).ground.card = n:= by
      simp_all only [ge_iff_le]

    set h_contraction := IdealFamily.deletionToN nposi Fcont v Fvx2 h_cont2
    have h_cont_card3: h_contraction.ground.card = n := by
      simp_all only [ge_iff_le]
      dsimp [h_contraction]
      dsimp [IdealFamily.deletionToN]
      rw [finDropCardEq nposi v Fcont.ground Fvx2]
      exact h_cont_card

    dsimp [Fdel] at hcard1
    --#check (h_ind h_idealdeletion) hcard3
    let h_idealdeletion2 := h_ind h_idealdeletion hcard3
    --#check h_ind h_contraction
    let h_contraction2 := (h_ind h_contraction) h_cont_card3

    have eq1: ideal_degree F v = degree F.toSetFamily v := by
      simp only [ideal_degree, degree]
      
    have eq2: ideal_family_size F = number_of_hyperedges F.toSetFamily := by
      simp only [ideal_family_size, total_size_of_hyperedges]

    simp only [ge_iff_le, tsub_le_iff_right, zero_add, Fdel, Fcont] at h_idealdeletion2 h_contraction2  ⊢
    simp only [normalized_degree_sum] at h_idealdeletion2 h_contraction2  ⊢

    rw [IdealFamily.deletionToN_number nposi Fdel v Fvx hcard2] at h_idealdeletion2
    rw [IdealFamily.deletionToN_number nposi Fcont v Fvx2 h_cont2] at h_contraction2
    dsimp [h_idealdeletion] at h_idealdeletion2
    dsimp [h_contraction] at h_contraction2
    rw [deletion_total] at h_idealdeletion2 h_contraction2
    dsimp [Fdel] at h_idealdeletion2
    dsimp [Fcont] at h_contraction2
    rw [h_del_card] at h_idealdeletion2

    --以下の部分も場合分けの前に移動したほうがよいかも。
    --let total_del := (total_size_of_hyperedges ((@IdealFamily.deletionToN (Fin n) n nposi Fdel v Fvx hcard2):IdealFamily (Fin n)).1)
    set total_del := total_size_of_hyperedges (IdealDeletion.idealdeletion F v hv_left hcard0).1 with h_total_del
    --set number_del := (number_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi Fdel v Fvx hcard2).1) with number_del
    set number_del := (number_of_hyperedges (IdealDeletion.idealdeletion F v hv_left hcard0).1) with h_number_del
    --let total_cont := (total_size_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi Fcont v Fvx2 h_cont2).1)
    --set total_cont := total_size_of_hyperedges (IdealDeletion.contraction F.1 v hv_left hcard0) with h_total_cont
    set total_cont := total_size_of_hyperedges (IdealDeletion.contraction_ideal_family F v hv_singleton hcard0).toSetFamily with h_total_cont
    --let number_cont := (number_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi Fcont v Fvx2 h_cont2).1)
    --set number_cont := (number_of_hyperedges (IdealDeletion.contraction F.1 v hv_left hcard0)) with h_number_cont
    set number_cont := (number_of_hyperedges (IdealDeletion.contraction_ideal_family F v hv_singleton hcard0).toSetFamily) with h_number_cont
    set total := (total_size_of_hyperedges F.toSetFamily) with h_total
    set  number := (number_of_hyperedges F.toSetFamily) with h_number
    set degreev := (degree F.toSetFamily v) with h_degreev

    classical
    by_cases hv_hyperedge:(F.sets (F.ground \ {v}))
    ·   case pos =>
        have h_sum_have := (hyperedge_average_have F v hv_left hcard0) hv_hyperedge hv_singleton
        --have h_idealdeletion := (IdealDeletion.idealdeletion F v hv_left hcard0)
        --#check sum_have
        let number_have :=  hyperedge_count_deletion_contraction_have_z F v hv_left hcard0 hv_hyperedge hv_singleton

        simp only [ge_iff_le, tsub_le_iff_right, zero_add, Fdel, Fcont] at h_sum_have number_have 
        simp only [normalized_degree_sum] at h_sum_have number_have 
      
        --今になって考えてみれば、Fin nを使わずにground setの大きさで議論する方法の方が良かった。
        simp_all only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one, degreev, number,
          h_idealdeletion, Fdel, Fcont, h_contraction, total_del, number_del, total_cont, number_cont, total, number_have]
        linarith
        /-
        rw [←h_total_del] at *
        rw [←h_number_del] at *
        rw [←h_total_cont] at *
        rw [←h_number_cont] at *
        --#check h_cont_card
        dsimp [Fcont] at h_cont_card
        --(IdealDeletion.contraction_ideal_family F v hv_singleton hcard0).toSetFamily)　　.. h_contraction2の中身。
        --number_of_hyperedges (IdealDeletion.contraction F.toSetFamily v hv_left hcard0) ..ゴールはこれ。
        --でずれている。{x}がhyperedgeと仮定しないとcontraction_ideal_familyに統一できない。ここでは、hv_singletonが仮定されているので問題ない。
        --idealSumのtheorem hyperedge_average_have {α : Type} [DecidableEq α] [Fintype α]aの言明を変える。

        --rw [←h_total]
        rw [←h_number] at *
        rw [←h_degreev] at *
        --subst degreev
        --rw [h_idealdeletion2, h_contraction2, sum_have, number_have]
        rw [hcard] at *
        rw [hcard1] at * -- (IdealDeletion.idealdeletion F v hv_left hcard0).ground.card = n
        dsimp [IdealDeletion.contraction_ideal_family] at h_cont_card --(IdealDeletion.contraction F.toSetFamily v ⋯ hcard0).ground.card = n
        rw [h_cont_card] at *
        rw [h_cont_card2] at * --↑(total_size_of_hyperedges h_cont✝.toSetFamily) * 2 - ↑(number_of_hyperedges Fcont✝¹.toSetFamily) * ↑n ≤ 0
        rw [h_cont_card3] at * --(IdealFamily.deletionToN nposi Fcont v Fvx2 h_cont2).ground.card = n
        clear hcard hcard1 hcard2 hcard3 h_cont_card h_cont_card2 h_cont_card3 hn h_ge2 h_ind hcard0 
        clear h_contraction hv_hyperedge h_idealdeletion 
        clear Fvx2 h_cont h_cont2 

        linarith --[h_idealdeletion2, h_contraction2, hv_right,sum_have,number_have] hv_rightは使う？
        -/
    ·   case neg =>
        --hv_hyperedge:(F.sets (F.ground \ {v}))が成り立たないケース。hv_singleton : ¬F.sets {v}のケースかも。どちらも未解決。
        have h_sum_none := hyperedge_average_none F v hv_left hcard0 hv_hyperedge hv_singleton
        have number_none := hyperedge_count_deletion_contraction_none F v hv_left hcard0 hv_hyperedge hv_singleton

        simp only [ge_iff_le, tsub_le_iff_right, zero_add, Fdel, Fcont] at h_sum_none number_none 
        simp only [normalized_degree_sum] at h_sum_none number_none
        simp_all only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one, degreev, number, h_idealdeletion,
        Fdel, Fcont, h_contraction, total_del, number_del, total_cont, number_cont, total]
        linarith

  --case negがもう一つある。hv_singleton:(F.sets {v})が成り立たないケース。
  --hv_singleton:(F.sets {v})が成り立たないケース。tabでインデントを調整して見えるようになった。
  · case neg =>
    have degree_one: degree F.toSetFamily v = 1 := by
      exact degree_one_if_not_hyperedge F hv_left hv_singleton
    --次数1があったからといって、normalized_degree_sumが負になるとはすぐに言えない。ただし、次数1があるということは、vは全体集合のみを含む。
    --goal normalized_degree_sum F.toSetFamily ≤ 0
    rw [normalized_degree_sum]
    by_cases hv_hyperedge:(F.sets (F.ground \ {v}))
    · case pos =>
      have Fsets: ∀ s ∈ F.ground.powerset, F.sets s ↔ v ∉ s ∨ s = F.ground := by
        intro s hs
        simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset]
        apply Iff.intro
        · intro a
          let ground_assum := (hyperedges_not_through_v F.toSetFamily v hv_left degree_one F.univ_mem) s a
          tauto
        · intro a
          cases a with
          | inl h => 
            have sinc: s ⊆ F.ground.erase v := by
              intro x hx
              simp_all only [Finset.mem_erase, ne_eq]
              apply And.intro
              · apply Aesop.BuiltinRules.not_intro
                intro a
                subst a
                simp_all only
              · exact hs hx
            have FsetG: F.sets (F.ground.erase v) := by
              convert hv_hyperedge
              ext1 a
              simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
              apply Iff.intro
              · intro a_1
                simp_all only [not_false_eq_true, and_self]
              · intro a_1
                simp_all only [not_false_eq_true, and_self]
            have hsng: F.ground.erase v ≠ F.ground := by
              intro a
              simp_all only [Finset.erase_eq_self, not_true_eq_false]
             
            exact F.down_closed s (F.ground.erase v) FsetG hsng sinc
          | inr h_1 =>
            subst h_1
            simp_all only [subset_refl]
            exact F.univ_mem
      
      --setsが完全に分かったので、normalized_degree_sumを計算する。ファイルを分けるべきかもしれない。
      have number_eq: number_of_hyperedges F.toSetFamily = 2^(F.ground.card - 1) + 1 := by
        rw [Ideal.number_of_hyperedges]
     
        -- `v` を含まない部分集合を取り出す
        let A := Finset.filter (λ s=> v ∉ s) F.ground.powerset
        -- `s = F.ground` を満たす唯一の部分集合を取り出す
        let B : Finset (Finset (Fin (n + 1))) := {F.ground}

        -- `A` と `B` が互いに素であることを示す
        have h_disjoint : Disjoint A B :=
         by
           rw [Finset.disjoint_iff_ne]
           intros s₁ hs₁ s₂ hs₂ h_eq
           rw [Finset.mem_filter] at hs₁
           have h₁ : v ∉ s₁ := hs₁.2
           rw [Finset.mem_singleton] at hs₂
           subst hs₂
           subst h_eq
           simp_all only [ge_iff_le, Nat.reduceLeDiff]

        -- `A ∪ B = F.sets` であることを示す
        have h_union : A ∪ B = Finset.filter F.sets F.ground.powerset :=
          by
            rw [Finset.ext]
            intro s
            rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_singleton]
            constructor
            -- A または B に属する場合
            intro h
            cases h
            simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff,
              Finset.mem_singleton, not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false,
              not_false_eq_true, sdiff_eq_left, Finset.disjoint_singleton_right, or_false, Finset.mem_filter,
              subset_refl, true_or, and_self, A, B]
            rename_i h
            subst h
            simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff,
              Finset.mem_singleton, not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false,
              not_false_eq_true, sdiff_eq_left, Finset.disjoint_singleton_right, or_false, Finset.mem_filter,
              subset_refl, or_true, and_self, A, B]
            -- F.sets に属する場合
            intro hs
            simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff,
              Finset.mem_singleton, not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false,
              not_false_eq_true, sdiff_eq_left, Finset.disjoint_singleton_right, or_false, Finset.mem_filter,
              subset_refl, true_and, A, B]
            obtain ⟨left, right⟩ := hs
            simp_all only
    

        -- `A` のカードは `2 ^ (F.ground.card - 1)` であることを示す
        have h_A_card : A.card = 2 ^ (F.ground.card - 1) :=
          by
            dsimp [A]
            --rw [Finset.card_filter]
            have sub_lem: ∀ s :Finset (Fin (n+1)),s ∈ (Finset.filter (fun s => v ∉ s) F.ground.powerset) ↔ s ⊆ F.ground.erase v := by
              intro s
              simp_all only [Finset.mem_filter, Finset.mem_powerset]
              apply Iff.intro
              intro a
              simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.singleton_subset_iff, Finset.mem_singleton,
                not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false, not_false_eq_true,
                sdiff_eq_left, Finset.disjoint_singleton_right, or_false, Finset.mem_filter, Finset.mem_powerset,
                subset_refl, A, B]
              obtain ⟨left, right⟩ := a
              intro x hx
              simp_all only [Finset.mem_erase, ne_eq]
              apply And.intro
              · apply Aesop.BuiltinRules.not_intro
                intro a
                subst a
                simp_all only
              · exact left hx
              · intro h
                simp_all only [ge_iff_le, Nat.reduceLeDiff]
                exact Finset.subset_erase.mp h

            have sub_lem2: (Finset.filter (fun s => v ∉ s) F.ground.powerset).card = (Finset.filter (fun s => s ⊆ F.ground.erase v) F.ground.powerset).card := by
              simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff,
                 Finset.mem_singleton, not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false,
                 not_false_eq_true, sdiff_eq_left, Finset.disjoint_singleton_right, or_false, Finset.mem_filter, A, B]
              apply Finset.card_bij (fun s hs => s)

               (by
                intro s hs
                simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff,
                  Finset.mem_singleton, not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false,
                  not_false_eq_true, sdiff_eq_left, Finset.disjoint_singleton_right, or_false, Finset.mem_filter, A, B]
                constructor
                rw [Finset.mem_filter] at hs
                rw [Finset.mem_powerset] at hs
                exact hs.1
                simp_all only [Finset.mem_filter, Finset.mem_powerset]
                
               )
               (by
                intro s hs
                simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff,
                  Finset.mem_singleton, not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false,
                  not_false_eq_true, sdiff_eq_left, Finset.disjoint_singleton_right, or_false, Finset.mem_filter, A, B]
                intro a₂ ha₂ a
                subst a
                trivial
                
               )
               /-
               (by --単車性
                intro s₁ hs₁ s₂ hs₂ h_eq
                simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff,
                  Finset.mem_singleton, not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false,
                  not_false_eq_true, sdiff_eq_left, Finset.disjoint_singleton_right, or_false, Finset.mem_filter, A, B]
                exact h_eq
               )
               -/
               (by
                intro s hs
                simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff,
                  Finset.mem_singleton, not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false,
                  not_false_eq_true, sdiff_eq_left, Finset.disjoint_singleton_right, or_false, Finset.mem_filter, A, B]
                constructor
                simp_all only [exists_prop]
                apply And.intro
                on_goal 2 => {rfl
                }
                · simp_all only
               )

            rw [sub_lem2]
            
            have h_eq : Finset.filter (fun s => s ⊆ F.ground.erase v) F.ground.powerset = (F.ground.erase v).powerset := by
               apply Finset.ext
               intro s
               constructor
               { -- (→) s ∈ Finset.filter (s ⊆ FG.erase v) FG.powerset ならば s ∈ (FG.erase v).powerset
                 intro hs
                 simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff,
                   Finset.mem_singleton, not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff,
                   and_false, not_false_eq_true, sdiff_eq_left, Finset.disjoint_singleton_right, or_false,
                   Finset.mem_filter, A, B]
               }
               { -- (←) s ∈ (FG.erase v).powerset ならば s ∈ Finset.filter (s ⊆ FG.erase v) FG.powerset
                 intro hs
                 rw [Finset.mem_powerset] at hs
                 
                 rw [Finset.mem_filter]
                 constructor
                 { -- s ⊆ FG.erase v
                    rw [Finset.mem_powerset]
                    exact (Finset.subset_erase.mp hs).1
                 }
                 { -- s ∈ FG.powerset
                    exact hs
                 }
               }
  
            -- 2. 冪集合のカーディナリティを計算する
            rw [h_eq] -- フィルタリングされた集合を FG.erase v の冪集合に置き換える
            rw [Finset.card_powerset] -- 冪集合のカーディナリティは 2^n
  
            -- 3. FG.erase v のカーディナリティが FG.card - 1 であることを示す
            have h_card : (F.ground.erase v).card = F.ground.card - 1 := Finset.card_erase_of_mem hv_left
            rw [h_card] -- 2^(FG.erase v).card を 2^(FG.card - 1) に置き換える
            --intro s
            
      

        -- `B` のカードは 1 であることを示す
        have h_B_card : B.card = 1 := Finset.card_singleton F.ground

        -- 最後に、カードの合計を求める
        --search_proof h_A_card h_B_card h_disjoint h_union number
        --rw [←(Finset.card_union), h_disjoint, h_union, h_A_card, h_B_card]
        rw [←h_union]
        rw [Finset.card_union_of_disjoint h_disjoint]
        rw [h_A_card,h_B_card]
      --ここまででnumberが求まった。これからtotalの方を求める。

      --AとBに分けて、それぞれのtotalを求める。Finset.sum_card_powersetを使う。
      have total_eq: total_size_of_hyperedges F.toSetFamily = (F.ground.card - 1)*2^(F.ground.card - 2) + F.ground.card := by
        rw [Ideal.total_degone_card F.toSetFamily v hv_left degree_one F.univ_mem hcard0]
        simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff, Finset.mem_singleton,
         not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false, not_false_eq_true, sdiff_eq_left,
         Finset.disjoint_singleton_right, or_false, add_tsub_cancel_right, Nat.reduceSubDiff, add_left_inj]
        --goal (Finset.filter (fun s => F.sets s ∧ v ∉ s) F.ground.powerset).sum Finset.card = n * 2 ^ (n - 1)
        let A := Finset.filter (λ s=> v ∉ s) F.ground.powerset
        -- `s = F.ground` を満たす唯一の部分集合を取り出す
        let B : Finset (Finset (Fin (n + 1))) := {F.ground}
        have total_lem: (Finset.filter (fun s => F.sets s ∧ v ∉ s) F.ground.powerset) = (F.ground.erase v).powerset := by
          apply Finset.ext
          intro s
          constructor
          { -- (→) s ∈ Finset.filter (s ⊆ FG.erase v) FG.powerset ならば s ∈ (FG.erase v).powerset
            intro hs
            simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff,
              Finset.mem_singleton, not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff,
              and_false, not_false_eq_true, sdiff_eq_left, Finset.disjoint_singleton_right, or_false,
              Finset.mem_filter, A, B]
            obtain ⟨left, right⟩ := hs
            obtain ⟨left_1, right⟩ := right
            simp_all only [not_false_eq_true, true_or]
            intro x hx
            simp_all only [Finset.mem_erase, ne_eq]
            apply And.intro
            · apply Aesop.BuiltinRules.not_intro
              intro a
              subst a
              simp_all only
            · exact left hx
          }
          { -- (←) s ∈ (FG.erase v).powerset ならば s ∈ Finset.filter (s ⊆ FG.erase v) FG.powerset
            intro hs
            rw [Finset.mem_powerset] at hs
            rw [Finset.mem_filter]
            constructor
            { -- s ⊆ FG.erase v
              rw [Finset.mem_powerset]
              exact (Finset.subset_erase.mp hs).1
            }
            { -- s ∈ FG.powerset
              
              let hxg := (Finset.subset_erase.mp hs).1
              let fx := Fsets s hxg
              let hxs := (Finset.subset_erase.mp hs).2
              constructor
              exact fx.mpr (Or.inl hxs)
              exact hxs
            }
          }
        rw [total_lem]

        have formula  :(F.ground.erase v).powerset.sum Finset.card = (F.ground.erase v).card * 2 ^ ((F.ground.erase v).card - 1) :=
          by
            
           -- 各要素が 2^(FG.card - 1) 回出現することを利用。hv_left : v ∈ F.groundも使うかも。
           --rw [← Finset.sum_const_nat]
           
           simp [Finset.card_powerset, mul_comm]
           --goal (F.ground.erase v).powerset.sum Finset.card = n * 2 ^ (n - 1)
        --#check Finset.sum_powersetCard
        --convert Finset.sum_powersetCard (F.ground.erase v)

        

        
          

    simp only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one] at hv_singleton degree_one ⊢ 
    --lemma total_degone_card {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground)(gcard: F.ground.card ≥ 2) :
    --total_size_of_hyperedges F = (F.ground.powerset.filter (λ s => F.sets s ∧ v ∉ s )).sum Finset.card + F.ground.card 
    rw [Ideal.total_degone_card F.toSetFamily v hv_left degree_one F.univ_mem hcard0]
    rw [Ideal.erase_ground_card F.toSetFamily v hv_left degree_one]
    let delF := IdealDeletion.deletion F.toSetFamily v hv_left hcard0
    have hvf: v ∉ delF.ground := by
      intro h
      simp_all only [ge_iff_le]
      dsimp [delF] at h
      rw [IdealDeletion.deletion] at h
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true]
    have hcard1: delF.ground.card = n := by
      simp_all only [ge_iff_le]
      simp_all only [delF]
      rw [IdealDeletion.idealdeletion]
      simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]
    have hcard2: delF.ground.card ≥ 1 := by
      simp_all only [ge_iff_le, delF]

    let ineq := h_ind  (@IdealFamily.deletionToN (Fin n) n nposi delF v hvf hcard2) (by
      simp_all only [ge_iff_le]
      simp_all only [IdealFamily.deletionToN]
      simp_all only [ge_iff_le, delF]
      -- hcard F.ground.card = n + 1
      --#check Ideal.IdealDeletion.ground_deletion F v hv_left hcard0
      --(IdealDeletion.idealdeletion F v hv_left hcard0).ground.card = F.ground.card - 1
      --#check finDropCardEq nposi v (IdealDeletion.idealdeletion F v hv_left hcard0).ground hvf
      --Ideal.finDropCardEq {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (s : Finset (Fin (n + 1))) (hvx : v ∉ s) :
      -- (Finset.image (finDrop nposi v) s).card = s.card - 1
      calc
        (Finset.image (finDrop nposi v) (IdealDeletion.idealdeletion F v hv_left hcard0).ground).card
      = ((IdealDeletion.idealdeletion F v hv_left hcard0).ground).card := by
          exact finDropCardEq nposi v (IdealDeletion.idealdeletion F v hv_left hcard0).ground hvf
    _ = n := by
          simp_all only [ge_iff_le]
    )
    rw [normalized_degree_sum] at ineq
    simp only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one] at ineq
    --rw [Ideal.total_degone_card] at ineq
    --Fin nとFin n+1の変換にIdealFamily.deletionToN_numberは必要かも。不等式系はFin n+1の世界にそろえればいいか。
    rw [IdealFamily.deletionToN_number nposi delF v hvf hcard2] at ineq
    --ineqの方の変数と、ゴールの方の変数が同じものを指すものがあるので、それを補題として示す。
    --集合族のレベルでなく数のレベルで示すとなると、また全単車を構成する必要がある。既存の定理が利用できないか。
    have total_eq: total_size_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi delF v hvf hcard2).toSetFamily = (Finset.filter (fun s => v ∉ s ∧ F.sets s) F.ground.powerset).sum Finset.card := by
      simp_all only [ge_iff_le]
      --simp_all only [IdealFamily.deletionToN]
      rw [deletion_total]
      dsimp [delF]
      dsimp [total_size_of_hyperedges]
      dsimp [IdealDeletion.idealdeletion]

      simp_all only [ge_iff_le, delF]
      --#check Ideal.total_degone_card
      --Ideal.total_degone_card {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground)(gcard: F.ground.card ≥ 2) :
      --total_size_of_hyperedges F = (F.ground.powerset.filter (λ s => F.sets s ∧ v ∉ s )).sum Finset.card + F.ground.card 
      dsimp [total_size_of_hyperedges]
      dsimp [IdealFamily.deletionToN]
      
      --(imageEq_card nposi F.toSetFamily v)はcardなのでsumでは使えない。imageEqのsum版なのでsum_bijが必要かも。その他の方法が思い浮かばない。
      apply sum_bij
      --bijective関係の証明
       fun s => finDrop nposi v s
      --goal ∀ (a : Finset (Fin n)) (ha : a ∈ (Finset.filter (λ (s : Finset (Fin (n + 1))), F.sets s) (F.ground.powerset)), finDrop nposi v a ∈ (Finset.filter (λ (s : Finset (Fin n)), F.sets s ∧ v ∉ s) (F.ground.powerset))
       intro s hs
       simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, and_self, implies_true, and_true, Finset.mem_image, Finset.mem_powerset, not_exists, not_and]

end Ideal
