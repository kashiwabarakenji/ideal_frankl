--Ideal集合族が平均abundantにならないことの証明が目標。まだうまく行ってないが保留にする。
import Mathlib.Data.Finset.Basic --hiding eq_empty_of_subset_empty
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
    -- ここで、finDrop (⟨x.val + 1, _⟩) = ⟨x.val, _⟩ となる。よって、finDrop_expand_inverse が成立
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

lemma example_ineq (k : ℕ) :
  (k + 1) * 2^(k + 1) + 2 * (k + 2) + (2 ^ (k + 1) - (k + 2)) = (2 ^ (k + 1) + 1) * (k + 2) := by
    have basic_ineq (n : ℕ) (h : 1 ≤ n) : 2^n≥n+1 :=
        by
          induction n with
          | zero =>
            -- 基底ケース: n = 0 は不適
            by_contra h_zero
            simp_all only [nonpos_iff_eq_zero, one_ne_zero]

          | succ k ih =>
          -- 帰納段階: n = k + 1 を証明
          -- 目標: 2^(k + 1) ≥ k + 2
          -- 2^(k + 1) = 2 * 2^k ≥ 2 * (k + 1) = k + 2
          have k_geq_0 : k ≥ 0 := by
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le]


          rw [pow_succ 2 k]

          by_cases h1: k = 0
          case pos =>
            rw [h1]
            simp_all only [Nat.one_pow, Nat.one_add]
            linarith
          case neg =>
          have hh1: k ≥ 1 := by
            simp_all only [ge_iff_le]
            omega
              -- 2^(k + 1) = 2 * 2^k
          have : 2 * 2^k ≥ 2 * (k + 1) := mul_le_mul_of_nonneg_left (ih hh1) (by norm_num)

          -- 2 * (k + 1) = k + 1 + k + 1 = 2k + 2 ≥ k + 2
          -- これは k ≥ 0 で常に成り立つ
          have : 2 * (k + 1) ≥ k + 2 := by
           calc
             2 * (k + 1) = k + 1 + k + 1 := by ring
             _ = (k + k) + (1 + 1) := by
               simp_all only [ge_iff_le, true_implies, le_add_iff_nonneg_left, zero_le, Nat.ofNat_pos, mul_le_mul_left,
               Nat.reduceAdd, add_left_inj]
               omega
             _ ≥ k + 2  := by
                simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
                omega
          simp_all only [ge_iff_le, true_implies, le_add_iff_nonneg_left, zero_le, Nat.ofNat_pos, mul_le_mul_left]
          omega
    have hh1: k + 1 ≥ 1 := by
      simp_all only [ge_iff_le]
      omega

    have add_sub_assoc (nn mm kk : ℕ) (h : mm ≥ kk) : nn + (mm - kk) = (nn + mm) - kk :=
      by
        rw [←Nat.add_sub_cancel' h]
        simp_all only [ge_iff_le, add_tsub_cancel_of_le]
        omega

    calc
    (k + 1) * 2^(k + 1) + 2 * (k + 2) + (2 ^ (k + 1) - (k + 2))
      = 2^(k + 1) * (k + 1) + 2 * (k + 2) + (2 ^ (k + 1) - (k + 2)) := by ring_nf
    _ = (2^(k + 1) * (k + 1) + 2*k + 4) + (2 ^ (k + 1) - (k + 2)) := by ring_nf
    _ = ((2^(k + 1) * (k + 1) + 2*k + 4) + 2 ^ (k + 1)) - (k + 2) := by
      --#check add_sub_assoc (2^(k + 1) * (k + 1) + 2*k + 4) (2 ^ (k + 1)) (k + 2) (basic_ineq (k+1) hh1)
      rw [add_sub_assoc (2^(k + 1) * (k + 1) + 2*k + 4) (2 ^ (k + 1)) (k + 2) (basic_ineq (k+1) hh1)]
    _ = 2^(k + 1) * (k + 1) + 2^(k + 1) + 2*k + 4 - (k + 2) := by ring_nf
    _ = 2^(k + 1) * (k + 1 + 1) + 2 * k + 4 - (k + 2) := by ring_nf
    _ = 2^(k + 1) * (k + 2) + (2 * k + 4 - (k + 2)) := by
      simp_all only [ge_iff_le, Nat.reduceSubDiff]
      ring_nf
      omega
    _ = 2^(k + 1) * (k + 2) + (2 * (k + 2) - (k + 2)) := by ring_nf
    _ = 2^(k + 1) * (k + 2) + (k + 2) := by
      simp_all only [ge_iff_le, Nat.reduceSubDiff]
      ring_nf
      omega
    _ = (2^(k + 1) + 1) * (k + 2) := by
      ring_nf

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
      have total := ground_minus_v_ideal_total F v hv_left hv_hyperedge hv_singleton hcard0
      have number := ground_minus_v_ideal_number F v hv_left hv_hyperedge hv_singleton
      rw [total, number]
      simp_all only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one]
      simp_all

      have basic_ineq (n : ℕ) (h : 1 ≤ n) : 2^n≥n+1 :=
        by
          induction n with
          | zero =>
            -- 基底ケース: n = 0 は不適
            by_contra h_zero
            simp_all only [nonpos_iff_eq_zero, one_ne_zero]

          | succ k ih =>
          have k_geq_1 : k ≥ 0 := by
              simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le]

          rw [pow_succ 2 k]

          by_cases h1: k = 0
          case pos =>
            rw [h1]
            simp_all only [Nat.one_pow, Nat.one_add]
            linarith
          case neg =>
          have hh1: k ≥ 1 := by
            simp_all only [ge_iff_le]
            omega
              -- 2^(k + 1) = 2 * 2^k
          have : 2 * 2^k ≥ 2 * (k + 1) := mul_le_mul_of_nonneg_left (ih hh1) (by norm_num)

          -- 2 * (k + 1) = k + 1 + k + 1 = 2k + 2 ≥ k + 2  これは k ≥ 0 で常に成り立つ
          have : 2 * (k + 1) ≥ k + 2 := by
           calc
             2 * (k + 1) = k + 1 + k + 1 := by ring
             _ = (k + k) + (1 + 1) := by
               simp_all only [ge_iff_le, true_implies, le_add_iff_nonneg_left, zero_le, Nat.ofNat_pos, mul_le_mul_left,
               Nat.reduceAdd, add_left_inj]
               omega
             _ ≥ k + 2  := by
                simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
                omega
          simp_all only [ge_iff_le, true_implies, le_add_iff_nonneg_left, zero_le, Nat.ofNat_pos, mul_le_mul_left]
          omega

      --以下はゴールと同じ。帰納法で示す必要あり。
      have inequality_example:
         (n * 2^(n - 1) + (n + 1)) * 2 ≤ (2^n + 1) * (n + 1) := by
        induction n with
        | zero =>
          -- 基底ケース: n = 0 は不適
          by_contra h_zero
          simp_all only [nonpos_iff_eq_zero, one_ne_zero]
        | succ k ih =>
        -- 帰納段階: n = k + 1 を証明
        -- 目標:((k + 1) * 2^k + (k + 2)) * 2 ≤ (2^(k + 1) + 1) * (k + 2)
          simp_all
          by_cases h1: k = 0
          case pos =>
            rw [h1]
            simp_all only [Nat.one_pow, Nat.one_add]
            subst h1
            simp_all only [nonpos_iff_eq_zero, one_ne_zero, zero_le, tsub_eq_zero_of_le, pow_zero, mul_one, zero_add,
              one_mul, Nat.reduceAdd, le_refl, false_implies, Nat.reduceMul, pow_one]
          case neg =>
          --以下はコメントアウトするとエラー
          have hh1: k ≥ 1 := by
            simp_all only [ge_iff_le]

          calc
              ((k + 1) * 2^k + (k + 2)) * 2
            = (k + 1) * 2^(k + 1) + 2 * (k + 2) := by ring
         _  = (k + 1) * 2^(k + 1) + 2 * (k + 2) + (2 ^ (k+1)-(k+2)) - (2^(k+1) - (k+2))   := by simp_all only [true_implies, ge_iff_le, le_add_iff_nonneg_left, zero_le, add_tsub_cancel_right]
         _  = (2^(k + 1) + 1) * (k + 2) - (2^(k+1) - (k+1)-1) := by
               rw [example_ineq k]
               simp_all only [true_implies, ge_iff_le, le_add_iff_nonneg_left, zero_le]
               rfl
         _  ≤ (2^(k + 1) + 1) * (k + 2) := by
                simp_all only [true_implies, ge_iff_le, le_add_iff_nonneg_left, zero_le]
                omega

      convert inequality_example
      simp_all only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one]
      simp_all only [iff_true]
      linarith
      --by_cases hv_hyperedge:(F.sets (F.ground \ {v}))のcase posの場合の証明おわり

    · case neg => --by_cases hv_hyperedge:(F.sets (F.ground \ {v}))のcase negの場合の証明
      --idealDelFとFでnumber_of_hyperedgesが同じになることを示す。
      --idealDelFとFでtotal_size_of_hyperedgesが1つちがいになることを示す。
      --idealDefFのnormalized_degree_sumが非負のとき、Fも非負であることを示す。
      simp only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one] at hv_singleton degree_one ⊢
      --lemma total_degone_card {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground)(gcard: F.ground.card ≥ 2) :
      --total_size_of_hyperedges F = (F.ground.powerset.filter (λ s => F.sets s ∧ v ∉ s )).sum Finset.card + F.ground.card
      rw [Ideal.total_degone_card F.toSetFamily v hv_left degree_one F.univ_mem hcard0]
      rw [Ideal.erase_ground_card F.toSetFamily v hv_left degree_one]

      let idealDelF := IdealDeletion.idealdeletion F v hv_left hcard0
      --delFじゃなくidealFに統一する。

      have hvfideal: v ∉ idealDelF.ground := by
        intro h
        simp_all only [ge_iff_le]
        dsimp [idealDelF] at h
        rw [IdealDeletion.idealdeletion] at h
        simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true]

      have hcard1ideal: idealDelF.ground.card = n := by
        simp_all only [ge_iff_le]
        simp_all only [idealDelF]
        --goal ((F.toSetFamily ∖ v) hv_left hcard0).ground.card = n
        dsimp [IdealDeletion.idealdeletion]
        simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]

      have hcard2ideal: idealDelF.ground.card ≥ 1 := by
        simp_all only [ge_iff_le, idealDelF]

      let ineq := h_ind  (@IdealFamily.deletionToN (Fin n) n nposi idealDelF v hvfideal hcard2ideal) (by
        simp_all only [ge_iff_le]
        simp_all only [IdealFamily.deletionToN]
        simp_all only [ge_iff_le]
        --#check finDropCardEq nposi v (IdealDeletion.idealdeletion F v hv_left hcard0).ground hvf
        --Ideal.finDropCardEq {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (s : Finset (Fin (n + 1))) (hvx : v ∉ s) :
        -- (Finset.image (finDrop nposi v) s).card = s.card - 1
        calc
          (Finset.image (finDrop nposi v) (IdealDeletion.idealdeletion F v hv_left hcard0).ground).card
        = ((IdealDeletion.idealdeletion F v hv_left hcard0).ground).card := by
            exact finDropCardEq nposi v (IdealDeletion.idealdeletion F v hv_left hcard0).ground hvfideal
      _ = n := by
            simp_all only [ge_iff_le]
      )
      rw [normalized_degree_sum] at ineq
      simp only [ge_iff_le, tsub_le_iff_right, zero_add, Nat.cast_add, Nat.cast_one] at ineq
      --rw [Ideal.total_degone_card] at ineq
      --Fin nとFin n+1の変換にIdealFamily.deletionToN_numberは必要かも。不等式系はFin n+1の世界にそろえればいいか。
      rw [IdealFamily.deletionToN_number nposi idealDelF v hvfideal hcard2ideal] at ineq
      --ineqの方の変数と、ゴールの方の変数が同じものを指すものがあるので、それを補題として示す。
      --集合族のレベルでなく数のレベルで示すとなると、また全単車を構成する必要がある。既存の定理が利用できないか。
      --以下は言明が間違っているかも。証明にはsum_bijを利用するかも。
      have number_eq: number_of_hyperedges F.toSetFamily = number_of_hyperedges idealDelF.toSetFamily := by
        dsimp [number_of_hyperedges,idealDelF]
        rw [IdealDeletion.idealdeletion]
        simp_all only [Finset.card_erase_of_mem, add_tsub_cancel_right]
        --goal: (Finset.filter F.sets F.ground.powerset).card =
        --(Finset.filter (fun s => F.sets s ∧ v ∉ s ∨ s = F.ground.erase v) (F.ground.erase v).powerset).card
        let domain := Finset.filter (λ (s:Finset (Fin (n+1))) => F.sets s) (F.ground.powerset)
        let range := Finset.filter (λ (s:Finset (Fin (n+1))) => (F.sets s ∧ v ∉ s) ∨ s = F.ground.erase v) (F.ground.erase v).powerset
        --#check Finset.card_bij
        --Finset.card_bij.{u_1, u_2} {α : Type u_1} {β : Type u_2} {s : Finset α} {t : Finset β} (i : (a : α) → a ∈ s → β)
        --(hi : ∀ (a : α) (ha : a ∈ s), i a ha ∈ t)
        --(i_inj : ∀ (a₁ : α) (ha₁ : a₁ ∈ s) (a₂ : α) (ha₂ : a₂ ∈ s), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
        --(i_surj : ∀ b ∈ t, ∃ a, ∃ (ha : a ∈ s), i a ha = b) : s.card = t.card
        set i := (λ (s : Finset (Fin (n+1))) (_: s ∈ domain) => s.erase v) with h_i
        --v notin sの場合はそのままで、v in sの場合はs erase vとなる。
        have hi : ∀ (s : Finset (Fin (n+1))), (hs: s ∈ domain) → (i s hs) ∈ range:= by
          intro s hs'
          dsimp [i,range]
          rw [Finset.mem_filter]
          rw [Finset.mem_powerset]
          constructor
          simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, idealDelF, domain, i]
          obtain ⟨left, right⟩ := hs'
          intro x hx
          simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
          obtain ⟨left_1, right_1⟩ := hx
          exact left right_1

          constructor
          dsimp [domain] at hs'
          rw [Finset.mem_filter] at hs'
          rw [Finset.mem_powerset] at hs'
          --hv_singletonからhyperedgeでvを含んでいるものは、全体集合のみ。
          by_cases s=F.ground
          case pos => --rangeのまたはの条件はどこにいったのか。
            dsimp [i,range]
            rename_i h
            subst h
            simp_all only [ge_iff_le, subset_refl, true_and, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
              not_false_eq_true, idealDelF, domain, i]
            search_proof
          case neg h_neg =>
            have vnotin: v ∉ s := by
              by_contra h_contra
              have v_subset_s: {v} ⊆ s := by
                simp_all only [ge_iff_le]
                rw [Finset.singleton_subset_iff]
                exact h_contra
              have v_hyperedge: F.sets {v} := by
                exact F.down_closed {v} s hs'.2 h_neg v_subset_s
              contradiction
            simp_all only [ge_iff_le, Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
            simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem, not_true_eq_false, and_self, idealDelF]

        have i_inj   (s : Finset (Fin (n+1))) (hs : s ∈ domain) (t : Finset (Fin (n+1))) (ht : t ∈ domain) : s.erase v = t.erase v → s = t:= by
          intro h_inj
          --sがvを含むかで場合分け。
          by_cases hv_in_s: v ∈ s
          · case pos =>
            by_cases hv_in_t: v ∈ t
            · case pos =>
              ext a
              apply Iff.intro
              · intro h
                simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, idealDelF, domain, i, hi]
                obtain ⟨left, right⟩ := hs
                by_cases hav: a = v
                case pos =>
                  rw [hav]
                  exact hv_in_t
                case neg =>
                  have asr: a ∈ s.erase v := by
                    rw [Finset.mem_erase]
                    constructor
                    exact hav
                    exact h
                  have atr: a ∈ t.erase v := by
                    rw [←h_inj]
                    exact asr
                  simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
              · intro h
                simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, idealDelF, domain, i, hi]
                obtain ⟨left, right⟩ := hs
                by_cases hav: a = v
                case pos =>
                  rw [hav]
                  exact hv_in_s
                case neg =>
                  have atr: a ∈ t.erase v := by
                    rw [Finset.mem_erase]
                    constructor
                    exact hav
                    exact h
                  have asr: a ∈ s.erase v := by
                    rw [h_inj]
                    exact atr
                  --simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
                    --have hsv: a ∈ s := by
                  rw [Finset.mem_erase] at asr
                  simp_all only [not_false_eq_true, Finset.mem_erase, ne_eq, and_self]

            · case neg =>
              --v in sということはsは全体集合であり、ground - vはhv_hyperedge : ¬F.sets (F.ground \ {v})の仮定よりhyperedgeではない。よって、h_inkに矛盾。
              have neg_lem: s = F.ground := by
                --hv_singleton : ¬F.sets {v}から言える。
                by_contra h_contra
                have v_subset_s: {v} ⊆ s := by
                  simp_all only [ge_iff_le]
                  rw [Finset.singleton_subset_iff]
                  exact hv_in_s
                have v_hyperedge: F.sets {v} := by
                  dsimp [domain] at hs
                  rw [Finset.mem_filter] at hs
                  rw [Finset.mem_powerset] at hs
                  exact F.down_closed {v} s hs.2 h_contra v_subset_s
                contradiction
              --s.erase v = t.erase vより、tは、groundかground-vである。
              have t_lem: t = F.ground ∨ t = F.ground.erase v := by
                subst neg_lem
                simp_all only [ge_iff_le, not_false_eq_true, Finset.erase_eq_of_not_mem, or_true, idealDelF,
                    i, hi]
                   --t_lemの証明おわり
              cases t_lem with
              | inl h1 =>
                subst h1 neg_lem
                simp_all only [ge_iff_le, not_true_eq_false, idealDelF, i, hi]
              | inr h2 =>
                --仮定htに矛盾
                rw [h2] at ht
                have : ¬F.sets (F.ground.erase v) := by
                  convert hv_hyperedge
                  exact Finset.erase_eq F.ground v
                dsimp [domain] at ht
                rw [Finset.mem_filter] at ht
                rw [Finset.mem_powerset] at ht
                let ht2 := ht.2
                contradiction

          · case neg => -- v ∉ sの場合
            by_cases hv_in_t: v ∈ t
            · case pos =>
              --v notin sということはsは全体集合であり、ground - vはhv_hyperedge : ¬F.sets (F.ground \ {v})の仮定よりhyperedgeではない。よって、h_inkに矛盾。
              have neg_lem: t = F.ground := by
                --hv_singleton : ¬F.sets {v}から言える。
                by_contra h_contra
                have v_subset_t: {v} ⊆ t := by
                  simp_all only [ge_iff_le]
                  rw [Finset.singleton_subset_iff]
                  exact hv_in_t
                have v_hyperedge: F.sets {v} := by
                  dsimp [domain] at ht
                  rw [Finset.mem_filter] at ht
                  rw [Finset.mem_powerset] at ht
                  exact F.down_closed {v} t ht.2 h_contra v_subset_t
                contradiction
              have s_lem: s = F.ground ∨ s = F.ground.erase v := by
                subst neg_lem
                simp_all only [ge_iff_le, not_false_eq_true, Finset.erase_eq_of_not_mem, or_true, idealDelF, i, hi]
              cases s_lem with
              | inl h1 =>
                subst h1 neg_lem
                simp_all only [ge_iff_le, not_true_eq_false, idealDelF, i, hi]
              | inr h2 =>
                rw [h2] at hs
                have : ¬F.sets (F.ground.erase v) := by
                  convert hv_hyperedge
                  exact Finset.erase_eq F.ground v
                subst neg_lem h2
                simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, and_false, idealDelF, domain,i, hi]

            · case neg =>
              simp_all only [ge_iff_le, not_false_eq_true, Finset.erase_eq_of_not_mem, idealDelF, i, hi]

        --示すものが違う気がする。
        have i_surj : ∀ (ss:Finset (Fin (n+1))), ss ∈ range → ∃ (s:Finset (Fin (n+1))), ∃ (hs : s ∈ domain), i s hs = ss := by
          intro ss hss
          have hv_notin_is: v ∉ ss:= by
            simp_all only [ge_iff_le]
            dsimp [i]
            simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, ne_eq, not_true_eq_false,
              false_and, not_false_eq_true, and_true, idealDelF, i]
            simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl, Finset.singleton_subset_iff,
              Finset.sdiff_subset, domain, range]
            obtain ⟨left, right⟩ := hss
            apply Aesop.BuiltinRules.not_intro
            intro a
            simp_all only [subset_refl, Finset.singleton_subset_iff, Finset.sdiff_subset, not_true_eq_false,
              and_false, false_or, Finset.mem_erase, ne_eq, and_true]

          by_cases hvs: v ∈ ss
          · case pos =>
            use F.ground
            have s_eq: ss = F.ground := by
              simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, not_false_eq_true, and_true, not_true_eq_false,
    idealDelF, i, hi]
            subst s_eq
            simp_all only [ge_iff_le, Finset.mem_filter, Finset.mem_powerset, not_false_eq_true, and_true, not_true_eq_false]
          · case neg =>
            rw [Finset.mem_filter] at hss
            rw [Finset.mem_powerset] at hss
            simp_all only [ge_iff_le, not_false_eq_true, and_true, Finset.erase_eq_of_not_mem, idealDelF, i, hi]
            --let hsscopy := hss
            have hsscopy := ss ∈ domain
            obtain ⟨left, right⟩ := hss
            cases right with
            | inl h =>
              --have ssh: i ss hsscopy = ss
              use ss
              simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl, not_false_eq_true,
                Finset.erase_eq_of_not_mem, domain]
              simp
              rw [Finset.subset_erase] at left
              exact left.1

            | inr h_1 =>
              use F.ground
              rw [h_1]
              simp
              dsimp [domain]
              rw [Finset.mem_filter]
              constructor
              subst h_1
              simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl, Finset.mem_erase, ne_eq,
                not_true_eq_false, and_true, not_false_eq_true, domain]
              exact F.univ_mem

        have bij := Finset.card_bij i hi i_inj i_surj  --idealSumを参考にするとdomainとrangeを設定したほうがいい。その間のbijectionを証明。
        --dsimp [domain, range] at bij
        simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, Finset.mem_erase, ne_eq, not_true_eq_false,
          false_and, not_false_eq_true, and_true, and_imp, subset_refl, exists_prop, Finset.singleton_subset_iff,
          Finset.sdiff_subset, idealDelF, domain, i, range]
        congr


      have total_eq: total_size_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi idealDelF v hvfideal hcard2ideal).toSetFamily = (Finset.filter (fun s => v ∉ s ∧ F.sets s) F.ground.powerset).sum Finset.card := by
        simp_all only [ge_iff_le]
        --simp_all only [IdealFamily.deletionToN]
        rw [deletion_total]
        dsimp [idealDelF]
        dsimp [total_size_of_hyperedges]
        dsimp [IdealDeletion.idealdeletion]

end Ideal
