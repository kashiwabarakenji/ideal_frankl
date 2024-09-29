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

/- ChatGPT o1-mini-1 の生成コード
-- Define the operation that restricts the SetFamily to those sets not containing `v`
def restrictToFin {n : Nat} (F : SetFamily (Fin (n+1))) (v : Fin (n+1)) : SetFamily (Fin n) :=
  let new_ground := F.ground.filter (λ x => x ≠ v) -- Remove v from the ground set
  let cast_pred (x : Fin (n+1)) : Option (Fin n) := if h : (x : Nat) < n then some ⟨x, h⟩ else none -- Casting function
  let new_ground_mapped := new_ground.attach.filterMap (λ ⟨x, _⟩ => cast_pred x) -- Map Fin (n+1) to Fin n
  {
    ground := new_ground_mapped,  -- Convert the filtered and mapped set back to a Finset
    sets := λ s => F.sets (s.map Fin.castSucc.toEmbedding) ∧ v ∉ s.map Fin.castSucc.toEmbedding,
    inc_ground := by
      intro s hs
      have h1 : s.map Fin.castSucc.toEmbedding ⊆ F.ground := by
        apply F.inc_ground
        exact hs.left
        --F.inc_ground (s.map (λ x => Fin.castSucc x)) hs.left
      exact map_subset_map _ _ h1,
    nonempty_ground := by
      obtain ⟨x, hx⟩ := F.nonempty_ground
      refine ⟨Option.get (cast_pred x), _⟩
      simp [cast_pred] at hx
  }
-/

def finDrop {n : ℕ} (nposi: n ≥ 1) (v : Fin (n + 1)) (x : Fin (n + 1)) : Fin n :=
  if h : x.val < v.val then
    ⟨x.val, by omega⟩
      --apply Nat.lt_succ_iff.2
      --exact Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ v.is_lt)⟩
  else
    ⟨x.val - 1, by omega⟩
     -- apply Nat.lt_of_lt_of_le (Nat.lt_succ_iff.2 (Nat.le_of_not_gt h)) (Nat.le_sub_left _ _)⟩

def finExpand {n : ℕ} (nposi: n ≥ 1) (v : Fin (n + 1)) (x : Fin n) : Fin (n + 1) :=
  if h : x.val < v.val then
    ⟨x.val, by omega⟩

  else
    ⟨x.val + 1, by omega⟩


lemma finDrop_expand_inverse {n : ℕ} (nposi : n ≥ 1) (v : Fin (n + 1)) (x : Fin n) :
  finDrop nposi v (finExpand nposi v x) = x := by
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
  y ≠ v → finExpand nposi v (finDrop nposi v y) = y := by
  unfold finDrop finExpand
  split_ifs with h
  · intro _ a
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
  v ∉ s.image (finExpand nposi v) := by
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
/-
lemma imageEq {n : ℕ} {s : Finset (Fin n)} (nposi : n ≥ 1)
  (F : SetFamily (Fin (n + 1))) (v : Fin (n + 1)) :
  F.sets (s.image (finExpand nposi v)) ↔
    s ∈ (F.ground.powerset.filter (λ ss => v ∉ ss ∧ F.sets ss)).image (Finset.image (finDrop nposi v)) := by
  simp only [Finset.mem_image]
  constructor
  -- 前向きの方向
  · --
    intro h
    set t := s.image (finExpand nposi v) with t_def
    have ht_sets : F.sets t := h
    have ht_ground : t ⊆ F.ground := F.inc_ground t ht_sets
    have hv_not_in_t : v ∉ t := finExpand_not_in nposi v s
    have s_eq : s = t.image (finDrop nposi v) := by
      ext x
      constructor
      · intro hx
        have : x = finDrop nposi v (finExpand nposi v x) := by
          exact (finDrop_expand_inverse nposi v x).symm

        rw [this]
        rw [Finset.mem_image]

        use finExpand nposi v x
        constructor
        rw [t_def]
        simp
        use x
        rfl

      · --goal x ∈ t.image (finDrop nposi v) → x ∈ s 下にある古いバージョンで証明されている？
        intro hx
        -- x が t.image finDrop に含まれるなら、finExpand x ∈ t であり、t = s.image finExpand なので finExpand x ∈ s.image finExpand
        rw [t_def] at hx
        rw [Finset.mem_image] at hx
        #check finDrop_expand_inverse nposi v x
        --rw [finDrop_expand_inverse nposi v x] at hx
        rcases hx with ⟨y, hy_in_t, hy_eq⟩
        -- hy_eq: y = finDrop nposi v x
        subst hy_eq
        simp_all only [Function.comp_apply, Finset.mem_image, t]
        simp_all only [not_exists, not_and]
        obtain ⟨w, h⟩ := hy_in_t
        obtain ⟨left, right⟩ := h
        subst right
        rw [finDrop_expand_inverse nposi v w]
        exact left

    rw [s_eq]
    use t
    constructor
    rw [Finset.mem_filter]
    constructor
    rw [Finset.mem_powerset]
    exact ht_ground
    constructor
    rw [t_def]
    unfold finExpand
    rw [Finset.mem_image]
    simp
    intro a1 hAx
    by_contra hh
    cases hh
    exact hh
    exact hAx

  -- 逆方向
  · --goal F.sets (Finset.image (finExpand nposi v) (Finset.image (finDrop nposi v) t))
    rintro ⟨t2, ht_sets, ht_filter, ht_image⟩
    simp_all only [Finset.mem_filter, Finset.mem_powerset]
    obtain ⟨left, right⟩ := ht_sets
    obtain ⟨left_1, right⟩ := right
    set s := t2.image (finDrop nposi v) with s_def
    have s_image_finExpand : s.image (finExpand nposi v) = t2 := by
      simp_all only [s]
      ext x1
      constructor
      intro hx
      simp_all only [Finset.mem_image, Function.comp_apply]
      obtain ⟨y, h⟩ := hx
      obtain ⟨left, right⟩ := h
      subst right
      obtain ⟨w, h⟩ := left
      obtain ⟨left, right_1⟩ := h
      subst right_1

      #check finDrop_expand_inverse nposi v w


      apply finExpand_drop_inverse nposi v

    finExpand_drop_inverse nposi v t2 (λ x hx => finExpand_not_in nposi v s hx) ht_sets
    rw [← s_image_finExpand]
    exact ht_sets

-/
--t ∈ F.ground.powersetがおかしい気がする。
lemma imageEq {n : ℕ} {s : Finset (Fin n)} (nposi : n ≥ 1)
  (F : SetFamily (Fin (n + 1))) (v : Fin (n + 1)) :
  F.sets (s.image (finExpand nposi v)) ↔
    s ∈ (F.ground.powerset.filter (λ ss => v ∉ ss ∧ F.sets ss)).image (Finset.image (finDrop nposi v)):= by
  simp only [Finset.mem_image, Finset.mem_image, Finset.mem_image, Finset.mem_image]
  constructor
  · intro h
    set t := s.image (finExpand nposi v) with t_def
    have t_ground : t ⊆ F.ground := by
      rw [t_def] at h
      exact F.inc_ground t h
    have ht_sets : F.sets t := h --これはtがgroundに含まれている事を示している？
    have ht_eq : s = t.image (finDrop nposi v) := by
      rw [Finset.image_image]
      ext x
      constructor
      · intro hx
        simp_all only [Finset.mem_image, Function.comp_apply, t]
        have : x = finDrop nposi v (finExpand nposi v x) :=
          by rw [finDrop_expand_inverse nposi v x]
        rw [this]
        -- finExpand x ∈ t なので finDrop (finExpand x) ∈ t.image finDrop
        use x
      · -- 右側: x ∈ t.image finDrop → x ∈ s
        intro hx
        -- x が t.image finDrop に含まれるなら、finExpand x ∈ t であり、t = s.image finExpand なので finExpand x ∈ s.image finExpand
        rcases Finset.mem_image.1 hx with ⟨y, hy_in_t, hy_eq⟩
        -- hy_eq: y = finDrop nposi v x
        subst hy_eq
        simp_all only [Function.comp_apply, Finset.mem_image, t]
        obtain ⟨w, h⟩ := hx
        obtain ⟨left, right⟩ := h
        -- finExpand y = x なので x ∈ s
        convert finDrop_expand_inverse nposi v y
        apply Iff.intro
        · intro a
          exact finDrop_expand_inverse nposi v y
        · intro a
          simp_all only
    rw [ht_eq]
    use t
    -- s = t.image finDrop により、s は (F.ground.powerset.filter F.sets).image (Finset.image finDrop) に属する
    -- t ∈ F.sets であり、t = s.image finExpand なので、s ∈ (F.ground.powerset.filter F.sets).image (Finset.image finDrop)
    --#check t.image (finDrop nposi v)
    --set tt := s.image (finExpand nposi v)
    constructor
    rw [Finset.mem_filter]
    constructor
    --goal t ∈ F.ground.powerset だけど成り立たないのでは？s grounfでも、t groundとは限らない。
    convert F.inc_ground t
    apply Iff.intro
    intro a
    intro a1
    exact t_ground
    intro a
    rw [Finset.mem_powerset]
    exact t_ground
    constructor
    rw [t_def]
    unfold finExpand
    rw [Finset.mem_image]
    simp
    intro a1 hAx
    by_contra hh
    cases hh
    exact hh
    exact hAx


  · intro h
    rcases h with ⟨t, ht_sets, ht_image⟩
    --この言明がおそらく成り立たない。v ∈ sを要求するが成り立たない。
    have hs_image_finExpand : t = s.image (finExpand nposi v) :=
      by
        ext x
        by_cases x_neq_v : x ≠ v
        constructor
        intro hx
        simp_all only [Finset.mem_image, Function.comp_apply]
        subst ht_image
        simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, exists_exists_and_eq_and]
        obtain ⟨left, right⟩ := ht_sets
        use x
        constructor
        simp_all only [ge_iff_le]

        -- x neq v
        exact finExpand_drop_inverse nposi v x x_neq_v

        simp at x_neq_v
        intro a1
        rw [Finset.mem_filter] at ht_sets
        subst ht_image
        simp_all only [Finset.mem_powerset, Finset.mem_image, exists_exists_and_eq_and]
        obtain ⟨left, right⟩ := ht_sets
        obtain ⟨w, h⟩ := a1
        obtain ⟨left_1, right⟩ := right
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

        --goal ⊢ x ∈ t ↔ x ∈ Finset.image (finExpand nposi v) s
        simp at x_neq_v
        rw [x_neq_v]
        apply Iff.intro
        intro a
        --simp_all only [Finset.mem_image, Function.comp_apply]
        subst ht_image
        simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, exists_exists_and_eq_and]
        obtain ⟨left, right⟩ := ht_sets
        use x
        constructor

        simp_all only [ge_iff_le]
        subst x_neq_v
        simp_all only [not_true_eq_false, false_and]

        simp at right
        intro a
        rw [←ht_image] at a
        --rw [Finset.mem_image] at a
        rw [Finset.mem_filter] at ht_sets
        --#check ht_sets.2.1
        -- goal: v ∈ sで仮定にそれの否定。
        rw [←x_neq_v] at ht_image
        simp_all only [Finset.mem_powerset, Finset.mem_image, exists_exists_and_eq_and]
        obtain ⟨left, right⟩ := ht_sets
        obtain ⟨w, h⟩ := a
        obtain ⟨left_1, right⟩ := right
        obtain ⟨left_2, right_1⟩ := h
        unfold finExpand at right_1
        by_cases hh: w > v
        case pos =>
          subst x_neq_v ht_image
          simp_all only [dite_eq_ite, Fin.coe_eq_castSucc, gt_iff_lt, Finset.mem_image]
          obtain ⟨w_1, h⟩ := left_2
          obtain ⟨left_2, right_2⟩ := h
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
          obtain ⟨left_2, right_2⟩ := h
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

    subst hs_image_finExpand
    simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, not_exists, not_and]






lemma finDropExpand {n : ℕ} (nposi: n >= 1) (v : Fin (n + 1)) (x:Fin n) : finDrop nposi v (finExpand nposi v x) = x :=
  by
    simp_all only [finDrop, finExpand]
    by_cases h: x.val < v.val
    case pos =>
      simp_all only [if_pos]
      simp_all only [↓reduceDIte, Fin.eta]
    case neg =>
      simp_all only [if_neg]
      simp_all only [↓reduceDIte, add_tsub_cancel_right, Fin.eta, dite_eq_right_iff]
      intro h_1
      ext1
      simp_all only [add_right_eq_self, one_ne_zero]
      simp_all only [ge_iff_le, not_lt]
      linarith

lemma finDropMonotone {n : ℕ} {A B: Finset (Fin (n + 1))}(nposi: n >= 1) (v : Fin (n + 1)) : A ⊆ B → A.image (finDrop nposi v) ⊆ B.image (finDrop nposi v) :=
  by
    intro h
    simp_all only [Finset.subset_iff, Finset.mem_image, and_imp]
    intro a ha
    obtain ⟨b, hb, hab⟩ := ha
    rw [←hab]
    subst hab
    exact ⟨b, h hb, rfl⟩

lemma finExpandMonotone {n : ℕ} {A B: Finset (Fin n)}(nposi: n >= 1) (v : Fin (n + 1)) : A ⊆ B → A.image (finExpand nposi v) ⊆ B.image (finExpand nposi v) :=
  by
    intro h
    simp_all only [Finset.subset_iff, Finset.mem_image, and_imp]
    intro a ha
    obtain ⟨b, hb, hab⟩ := ha
    rw [←hab]
    subst hab
    exact ⟨b, h hb, rfl⟩

lemma finDrop_expand_inverse {n : ℕ} (nposi : n ≥ 1)
  (v : Fin (n + 1)) (s : Finset (Fin n)) :
  (s.image (finExpand nposi v)).image (finDrop nposi v) = s :=
by
  -- finExpand と finDrop の定義に基づいて証明します
  -- 各要素 x ∈ s に対して finDrop (finExpand x) = x であることを示す
  ext x
  simp only [Finset.mem_image]
  constructor
  intro hx
  rcases hx with ⟨y, hy₁, hy₂⟩
  rw [finDrop_def]
  split_ifs with h
  -- x.val < v.val
  rw [hy₂]
  exact hy₁

  -- x.val ≥ v.val
      -- finDrop は x.val - 1 を返す
      -- しかし finExpand においては x.val < v.val の場合のみ定義されているため、この場合は存在しない
      -- よって、この場合は不可能
  --exfalso
      -- 具体的な証明は finExpand の完全な定義に依存します

  intro hx
  use finExpand nposi v x
  constructor
  -- finExpand の値が finExpand nposi v x であること
  exact Finset.mem_image_of_mem _ hx
  -- finDrop (finExpand x) = x
      -- finDrop_expand_inverse の性質を利用
      -- 実際には finDrop_expand_inverse を証明する必要があります
  rw [finDrop_def]
  split_ifs with h
  -- x.val < v.val
  search_proof
  -- x.val ≥ v.val
  -- 同様に、不可能な場合を扱う
  exfalso
  sorry



lemma imageEq {n : ℕ} {s : Finset (Fin n)} (nposi : n ≥ 1) (F : SetFamily (Fin (n + 1))) (v : Fin (n + 1)) :
  F.sets (s.image (finExpand nposi v)) ↔ s ∈ ((F.ground.powerset.filter F.sets).image (Finset.image (finDrop nposi v))) :=
  by
    simp_all only [Finset.mem_image, Finset.mem_image, Finset.mem_image, Finset.mem_image]
    constructor
    -- 左から右への方向
    intro h
    -- t を s.image finExpand として存在させる
    let t := s.image (finExpand nposi v)
    -- t が F.sets に含まれることは h から直接わかる
    have ht_sets : F.sets t := h
    -- s が t.image finDrop に等しいことを示す
    have ht_eq : s = t.image (finDrop nposi v) :=
      by
        -- finDrop と finExpand の逆写像性を利用して証明
        simp_all only [t]
        rw [Finset.image_image]
        ext x
        simp_all only [Finset.mem_image, Finset.mem_image, Finset.mem_image, Finset.mem_image]
        apply Iff.intro
        intro hx
        simp_all only [Function.comp_apply]
        on_goal 1 => exact ⟨x, hx, by rw [finDropExpand nposi v x]⟩
        intro a
        simp_all only [Function.comp_apply]
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        subst right
        convert finDropExpand nposi v w
        constructor
        intro h
        sorry --証明できない。finDropとfinExpandの逆写像性を示す補題が必要。
        intro a
        simp_all only

    -- 実際には finDrop と finExpand が互いの逆写像であることを示す必要がある
    -- ここでは直接等号を使って示します
    -- 例えば、finDrop_expand_inverse という補題があると仮定します
    -- もしない場合は、finDrop と finExpand の定義から直接証明する必要があります
    -- ここでは簡略化のために等号を使用します
    rw [ht_eq]
    -- これにより、s は F.ground.powerset.filter F.sets の image に含まれることがわかる
    exact ⟨t, ht_sets, rfl⟩

    -- 右から左への方向
    intro h
    -- h から t とその性質を取り出す
    rcases h with ⟨t, ht_sets, ht_image⟩
    -- s = t.image finDrop であることから、s.image finExpand = t であることを示す
    -- finDrop と finExpand が互いに逆写像であることを利用
    -- 具体的には finExpand を適用すると finDrop の逆写像になる
    have : t.image (finExpand nposi v) = s.image (finExpand nposi v).image finDrop nposi v :=
      by rw [Finset.image_image]
    -- finDrop と finExpand の逆写像性を用いる
    -- 具体的な補題が必要ですが、ここでは直接書きます
    -- 例えば、finDrop_expand_inverse が存在すると仮定
    -- 実際には finExpand と finDrop の定義から示す必要があります
    -- 簡略化のために等号を使用します
    rw [ht_image, Finset.image_image] at this
    -- 結果として F.sets (s.image finExpand) を得る
    exact ht_sets

def deletionToN {n : ℕ} (nposi : n ≥ 1) (F : SetFamily (Fin (n + 1))) (v : Fin (n + 1)) : SetFamily (Fin n) :=
{
  ground := F.ground.image (finDrop nposi v),
  sets := λ s=> F.sets (s.image (finExpand nposi v)),
  inc_ground := λ s hs =>
  by
    #check (F.ground.powerset.filter F.sets)
    #check (Finset.image (finDrop nposi v))
    --deletionしたものは、もともとのF.setsをfinDropしたものになっていることを示す必要あり。
    --goal s ⊆ Finset.image (finDrop nposi v) F.ground
    --finDropとfinExpandの定義を使うと証明できる？
    have goal: s ⊆ F.ground.image (finDrop nposi v) := by
      intro x hx
      simp_all only [Finset.mem_image, Finset.mem_image, Finset.mem_image, Finset.mem_image]
      exact finDropMonotone nposi v







      simp
    /-have ground_all: F.ground = Finset.univ:= by --たぶん成り立たない。
      simp_all only [Finset.mem_univ]
      ext y
      apply Iff.intro
      intro h
      simp_all only [Finset.mem_univ]
      #check F.ground
    -/

    have hInc0: finDrop nposi v v ∈ F.ground.image (finDrop nposi v) := by
      simp_all only [Finset.mem_image]
      by_cases h: v ∈ F.ground
      case pos =>
        exact ⟨v, h, rfl⟩
      case neg =>
        use v
        simp_all only [Fin.is_lt]
        simp_all
        --多分成田田ない。

      simp_all only [Fin.is_lt]
      simp_all only [Finset.mem_univ, implies_true]
    have hInc := F.inc_ground (s.image (finExpand nposi v)) hs
    rw [Finset.subset_iff] at *
    intro x hx
    simp_all only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    use v
    constructor
    have h1 : v.val < n + 1 := v.2
    have h2: v ∈ F.ground := by

      simp_all only [Fin.is_lt]
      simp_all only [Finset.mem_univ, implies_true]
    rw [ground_all] at h2
    exact h2
    simp_all only [Finset.mem_univ, implies_true]
    dsimp [finDrop]
    by_cases h : v.val < v.val
    case pos =>
      simp_all only [Nat.lt_irrefl]
    case neg =>
      simp_all only [not_lt]








    --rw [Finset.mem_image] at hx
    --rcases hx with ⟨y, hyInS, hxy⟩
    --rw [← hxy]
    --apply Finset.mem_image_of_mem
    --apply hInc
    --apply Finset.mem_image_of_mem
    --exact hyInS,
  nonempty_ground :=
  by
    obtain ⟨x, hx⟩ := F.nonempty_ground
    use finDrop nposi v x
    apply Finset.mem_image_of_mem
    exact hx,
  fintype_ground := by
    apply Fintype.ofFinset (Finset.image (finDrop nposi v) F.ground) (λ x=> by
    simp_all only [Finset.mem_image, Finset.image_val, Multiset.mem_dedup, Multiset.mem_map, Finset.mem_val]
    rfl),
}

-- IdealFamily (Fin (n + 1)) を IdealFamily (Fin n) に変換
def ideal_deletion_to_n {n : ℕ}(nposi: n >= 1) (F : IdealFamily (Fin (n + 1))) (v : Fin (n + 1)) : SetFamily (Fin n) :=
  -- 変換関数を適用して新しいIdealFamilyを作成
  let filtered_sets := Finset.filter (λ s : Finset (Fin (n + 1)) => F.sets s) F.ground.powerset
  SetFamily.mk
    --(Finset.image (λ s : Finset (Fin (n + 1)) => s.image (fin_drop nposi v)) filtered_sets)
    (F.ground.image (fin_drop nposi v))
    (λ s => F.sets (s.image (fin_expand nposi v)))
    (λ s hs => by
      simp_all only [ge_iff_le, filtered_sets]
      have nnposi: n + 1 >= 1 := by omega
      have h_subset : s ⊆ Finset.image (finDrop nposi v) F.ground := by
        intro x hx
        simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le, Finset.mem_image]
        have h1 : ∃ (a : Fin (n + 1)), a ∈ F.ground ∧ x = finDrop nposi v a := by
          simp_all only [Finset.mem_filter, Finset.mem_powerset] at hs
          exact hs x hx
        obtain ⟨y, hy, hy_eq⟩ := Finset.mem_image.mp (Finset.mem_of_subset (F.inc_ground (s.image (fin_expand nposi v)) hs) (Finset.mem_image_of_mem (fin_expand nposi v) hx))
        --obtain ⟨y, hy, hy_eq⟩ := Finset.mem_image.mp (Finset.mem_of_subset (F.inc_ground (s.image (fin_expand nposi v)) hs) (Finset.mem_image_of_mem (fin_expand nposi v) (Finset.mem_of_subset (F.inc_ground s hs))))
        rw [←hy_eq]
        exact Finset.mem_image_of_mem (fin_drop nposi v) hy
      exact h_subset
    )
    (by
      intro s hs
      --simp
      simp_all only [ge_iff_le, filtered_sets]

      --ext y
      constructor
      intro h
      simp at h
      cases h with
      |inl h1 => simp [h1]
      |inr h2 => simp [h2]
    )
    (by
      simp_all only [ge_iff_le, Finset.image_nonempty, filtered_sets]
      use ∅
      rw [Finset.mem_filter]
      constructor
      simp_all only [Finset.mem_powerset, Finset.empty_subset]
      exact F.empty_mem
    )
  -- F.toSetFamily.image (fin_drop nposi v)


def P (x:Nat) : Prop := x ≥ 2  ∧ ∀ (F: IdealFamily (Fin x)), F.ground.card = x → normalized_degree_sum F.toSetFamily ≤ 0


theorem induction_step {n:Nat} (hn: n >= 2) (h: P n) : P (n+1) := by
  -- ここでFintypeインスタンスを明示的に使用
  --have fintype_ground : Fintype F.ground := finF
  unfold P at h ⊢
  obtain ⟨h_ge2, h_ind⟩ := h

  constructor
  simp_all only [ge_iff_le, Nat.reduceLeDiff]
  --obtain ⟨left, right⟩ := h
  omega
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

  classical
  by_cases hv_hyperedge:(F.sets (F.ground \ {v}))
  case pos =>
    have h_sum_have := (hyperedge_average_have F v hv_left hcard0) hv_hyperedge
    have h_idealdeletion := (IdealDeletion.idealdeletion F v hv_left hcard0)
    --IdealFamily (Fin (n + 1))になっているがFin nになってほしい。
    have h_contraction :=  (IdealDeletion.contraction F.toSetFamily v hv_left hcard0)
    rw [h_sum_have]
    #check h_ind h_idealdeletion
    #check h_ind h_contraction

    linarith [h_idealdeletion, h_contraction, hv_right]









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

end Ideal
