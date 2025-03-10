--帰納法でFin (n+1)などを扱うのでそのための変換。そもそもFinを使う必要はなかったかも。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
--import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import Ideal.IdealDeletion
--import Ideal.IdealRare
--import Ideal.IdealSum
--import Ideal.IdealNumbers
--import Ideal.IdealDegreeOne
import LeanCopilot

namespace Ideal

variable {α : Type} [DecidableEq α] [Fintype α]

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
  simp only [ add_tsub_cancel_right]

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
      omega
    next h_1 =>
      ext1
      simp_all only
      omega

lemma finExpand_not_in {n : ℕ}(v : Fin (n + 1)) (s : Finset (Fin n)) :
  v ∉ s.image (finExpand  v) := by
  intro h
  simp at h
  obtain ⟨x, _, h_eq⟩ := h
  rw [finExpand, ← h_eq] at h_eq
  --simp_all only [ dite_eq_ite]
  split at h_eq
  next h =>
    split at h_eq
    next h_1 => simp_all only [lt_self_iff_false]
    next h_1 => simp_all only [not_false_eq_true, Fin.mk.injEq, add_right_eq_self, one_ne_zero]
  next h =>
    split at h_eq
    next h_1 =>
      simp_all only [ Fin.mk.injEq, self_eq_add_right]
      simp_all only [not_lt, add_zero, lt_self_iff_false]
    next h_1 => simp_all only [lt_add_iff_pos_right, zero_lt_one]--

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
  · simp only [Finset.mem_image]
    intro a
    simp only [exists_exists_and_eq_and] at a
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
      simp_all only [ Fin.mk.injEq]--
      omega
      -- ケース 2: x.val < v.val, y.val >= v.val の場合
      simp_all only [ Fin.mk.injEq]
      omega
      -- ケース 3: x.val >= v.val, y.val < v.val の場合
      simp_all only [ Fin.mk.injEq]
      omega
      -- ケース 4: 両方の x.val, y.val >= v.val の場合
      simp_all only [Fin.mk.injEq]
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
    simp only [Finset.subset_iff,Finset.mem_image]--
    intro a ha
    obtain ⟨b, hb, hab⟩ := ha
    rw [←hab]
    subst hab
    exact ⟨b, h hb, rfl⟩

lemma finExpandMonotone {n : ℕ} {A B: Finset (Fin n)} (v : Fin (n + 1)) : A ⊆ B → A.image (finExpand  v) ⊆ B.image (finExpand  v) :=
  by
    intro h
    simp only [Finset.subset_iff, Finset.mem_image]
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
  simp only [Finset.mem_image]
  constructor
  -- 方向 1: F.sets (s.image (finExpand nposi v)) → s ∈ (F.ground.powerset.filter ...).image (Finset.image (finDrop nposi v))
  · intro h
    set t := s.image (finExpand  v) with t_def  -- t = s.image (finExpand nposi v)
    have t_ground : t ⊆ F.ground := by
      rw [t_def] at h
      exact F.inc_ground t h
    have ht_sets : F.sets t := h  -- t が F.sets に属している
    -- s = t.image (finDrop nposi v) を示す
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
        subst hy_eq
        rw [finDrop_expand_inverse nposi v y]
        exact hy_in_t
      }
    -- s = t.image (finDrop nposi v) が得られたので、次に s がフィルタされた集合族に属することを示す
    use t
    constructor
    -- t が F.ground の部分集合であることを示す
    {
      rw [Finset.mem_filter]
      constructor
      rw [Finset.mem_powerset]
      exact t_ground
      constructor
      -- v ∉ t であることを示す
      have hv_not_in_t : v ∉ t := finExpand_not_in v s
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
    obtain ⟨_, right2⟩ := ht_sets
    have hs_image_finDrop : s = t.image (finDrop nposi v) := (ht_image).symm

    -- t = s.image (finExpand nposi v) を証明する
    have ht_image_finExpand : t = s.image (finExpand  v) := by
      ext x
      --constructor
      -- t に属する要素は、s を finExpand したものの像に含まれる

      by_cases x_neq_v : x ≠ v
      constructor
      intro hx
      subst ht_image
      simp only [ Finset.mem_image, exists_exists_and_eq_and]--

      use x
      constructor
      simp_all only [ge_iff_le]

      -- x neq v
      exact finExpand_drop_inverse nposi v x x_neq_v

      simp at x_neq_v
      intro a1
      subst ht_image
      simp_all only [ Finset.mem_image, exists_exists_and_eq_and]--
      obtain ⟨w, h⟩ := a1
      obtain ⟨left_1, _⟩ := right2
      obtain ⟨left_2, right_1⟩ := h
      subst right_1
      by_cases hh: w = v
      case pos =>
        subst hh
        simp_all only [ Function.comp_apply]
      case neg =>
        rw [finExpand_drop_inverse nposi v w hh]
        exact left_2

      simp at x_neq_v
      rw [x_neq_v]
      apply Iff.intro
      intro a
      subst ht_image
      simp_all only [Finset.mem_filter]

      intro a --mark 0
      rw [←ht_image] at a

      simp_all only [ Finset.mem_image]--
      obtain ⟨w, hh⟩ := a
      obtain ⟨left_1, _⟩ := right2
      obtain ⟨left_2, right_1⟩ := hh

      unfold finExpand at right_1
      by_cases hh: w > v
      case pos =>
        subst x_neq_v ht_image

        simp_all only [ Fin.coe_eq_castSucc,  Finset.mem_image]--
        obtain ⟨w_1, hhh⟩ := left_2
        obtain ⟨_, right_2⟩ := hhh
        subst right_2
        split at right_1
        next h =>
          apply left_1
          simp_all only
          exact hh.not_lt h
        next h =>
          simp_all only [not_lt]
          rw [← right_1] at h
          simp_all only [add_le_iff_nonpos_right, nonpos_iff_eq_zero]--
          simp_all only [  one_ne_zero]--
      case neg =>
          subst x_neq_v ht_image
          simp only [Finset.mem_image] at left_2
          obtain ⟨w_1, h⟩ := left_2
          obtain ⟨_, right_2⟩ := h
          subst right_2
          split at right_1
          next h =>
            rw [← right_1] at h
            simp_all only [lt_self_iff_false]
          rename_i h
          simp_all only [not_lt]--
          rw [← right_1] at h
          simp_all only [add_le_iff_nonpos_right, nonpos_iff_eq_zero]--
          simp_all only [ one_ne_zero]

    rw [←ht_image_finExpand]
    exact right2.2



lemma imageEq_card {n : ℕ} (nposi : n ≥ 1)
    (F : SetFamily (Fin (n + 1))) (v : Fin (n + 1)) :
    ((Finset.image (finDrop nposi v) F.ground).powerset.filter (λ s => F.sets (s.image (finExpand v)))).card =
      (F.ground.powerset.filter (λ ss => v ∉ ss ∧ F.sets ss)).card := by

  -- 定義域と共域のセットを明確にする
  let left_set := (Finset.image (finDrop nposi v) F.ground).powerset.filter (λ s => F.sets (s.image (finExpand v)))
  let right_set := (F.ground.powerset.filter (λ ss => v ∉ ss ∧ F.sets ss))

  -- バイジェクションを定義する
  let to_fun := λ s : Finset (Fin n) => s.image (finExpand v)

  --have bij1 : ∀ (s : Finset (Fin n)) (hs : s ∈ left_set), Finset (Fin (n + 1)) := λ s hs => to_fun s

  -- 1. to_fun は left_set の要素を right_set の要素に写すことを証明
  have bij1_proof : ∀ s ∈ left_set, to_fun s ∈ right_set := by
    intro s hs
    dsimp [right_set]
    rw [Finset.mem_filter]
    constructor
    -- v ∉ to_fun s の証明
    · simp_all only [Finset.mem_filter, Finset.mem_powerset, left_set]--
      obtain ⟨_, right⟩ := hs
      apply F.inc_ground
      exact right

    -- F.sets (to_fun s) の証明
    · constructor
      dsimp [to_fun]
      rw [Finset.mem_filter] at hs
      exact finExpand_not_in v s
      simp_all only [Finset.mem_filter, left_set]--


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
    simp_all only [ to_fun]
    rw [finExpand_drop_inverse_set nposi v b]
    exact left_1
    rw [Finset.mem_filter]
    constructor

    simp_all only [ Finset.mem_powerset]

    exact finDropMonotone nposi v left

    rw [finExpand_drop_inverse_set nposi v b]
    exact right_1

    exact left_1

  -- すべての条件を満たしているので、バイジェクションを示す

  dsimp [left_set] at bij3new
  --dsimp [left_set] at bij4
  exact Finset.card_bij (λ s _ => to_fun s) bij1_proof bij3new bij4new


def deletionToN {n : ℕ} (nposi : n ≥ 1) (F : SetFamily (Fin (n + 1))) (v : Fin (n + 1)) (_: v ∉ F.ground) (ground_ge_two: F.ground.card >= 1): SetFamily (Fin n) :=
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
    simp_all only [ Finset.one_le_card, Finset.image_nonempty, new_ground]--
 }


--こっちはidealFamilyからidealFamilyへの写像
def IdealFamily.deletionToN {n : ℕ} (nposi : n ≥ 1)
  (F : IdealFamily (Fin (n + 1))) (v : Fin (n + 1)) (hvf : v ∉ F.ground)
  (ground_ge_two : F.ground.card ≥ 1) : IdealFamily (Fin n) :=
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

  has_empty := by
    -- 空集合が必ず `sets` に含まれることを示す
    simp only [Finset.image_empty]
    exact F.has_empty,

  has_ground := by
    -- 全体集合が `sets` に含まれることを示す
    simp only [Finset.univ]
    simp_all only [  new_ground]
    rw [finExpand_drop_inverse_set nposi v]
    -- goal v ∉ F.ground
    -- goal F.sets F.ground
    exact F.has_ground
    simp_all only [not_false_eq_true]
    --exacts [finDrop_mem nposi, hvf]
    --exact F.has_ground,

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

    exact hB'

  nonempty_ground := by
    simp_all only [ Finset.one_le_card, Finset.image_nonempty, new_ground]
}

lemma IdealFamily.deletionToN_number {n : ℕ} (nposi : n ≥ 1)
  (F : IdealFamily (Fin (n + 1))) (v : Fin (n + 1)) (hvf : v ∉ F.ground)
  (ground_ge_two : F.ground.card ≥ 1) : number_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi F v hvf ground_ge_two).toSetFamily = number_of_hyperedges F.toSetFamily := by
  rw [number_of_hyperedges]
  simp_all only [IdealFamily.deletionToN]
  rw [number_of_hyperedges]
  --have nnposi: n + 1 ≥ 1 := by omega

  apply Eq.symm
  --以下はコメントアウトするとなぜかエラーが出る。
  have eqlem: (Finset.filter (λ s => F.sets (Finset.image (finExpand v) s)) (Finset.image (finDrop nposi v) F.ground).powerset).card = (Finset.filter (λ s => v ∉ s ∧ F.sets s) F.ground.powerset).card := by
    exact imageEq_card nposi F.toSetFamily v

  simp_all only [le_add_iff_nonneg_left]
  simp_all only [Finset.one_le_card]
  congr 1
  ext1 a
  simp only [Finset.mem_filter, Finset.mem_powerset, and_congr_right_iff, iff_and_self]--
  intro a_1 _
  apply Aesop.BuiltinRules.not_intro
  intro a_3
  exact hvf (a_1 a_3)

--下で使っている。
theorem sum_card_eq_sum_card  {n : ℕ} (F : IdealFamily (Fin (n+1))) (nposi : n ≥ 1)(v : Fin (n+1)) (hvf : v ∉ F.ground):
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
      simp_all only [Finset.mem_filter, Finset.mem_powerset, s_fin]--
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

  have h_injective: ∀ (a₁ : Finset (Fin (n + 1))) (ha₁ : a₁ ∈ s_fin) (a₂ : Finset (Fin (n + 1))) (ha₂ : a₂ ∈ s_fin),
  i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ :=
    by
      intros a₁ ha₁ a₂ ha₂ h
      simp_all only [Finset.mem_filter,  s_fin]--
      dsimp [i] at h
      simp_all only [  Finset.mem_filter, Finset.mem_powerset, s_fin]
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
    simp_all only [Finset.mem_powerset, i, t_fin]
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

lemma deletion_total: ∀ (n : ℕ) (F : IdealFamily (Fin (n + 1))) (nposi : n ≥ 1) (v : Fin (n + 1)) (hvf : v ∉ F.ground) (ground_ge_two : F.ground.card ≥ 1),
  total_size_of_hyperedges (@IdealFamily.deletionToN (Fin n) n nposi F v hvf ground_ge_two).toSetFamily = total_size_of_hyperedges F.toSetFamily :=
  by
    intros n F nposi v hvf ground_ge_two
    simp only [total_size_of_hyperedges]
    simp only [IdealFamily.deletionToN]
    have h2 := sum_card_eq_sum_card F nposi v hvf
    rw [h2]

---------------------------------
-- SetFamily 構造体の定義に基づいて、SetFamily (Fin n) への変換関数を定義します
noncomputable def SetFamily.toFinFamily {α : Type} [DecidableEq α] [Fintype α]
  (sf : SetFamily α) (n : ℕ) (h : Fintype.card sf.ground = n) : SetFamily (Fin n) :=
  let toFin : sf.ground ≃ Fin n := Fintype.equivFinOfCardEq h
  let embedding : {x // x ∈ sf.ground} → Fin n := toFin.toFun
  let groundFin : Finset (Fin n) := (sf.ground.attach).map ⟨toFin, by
    subst h
    simp_all only [toFin]
    exact toFin.injective
  ⟩
  {
    ground := groundFin,
    sets := λ s => ∃ t : Finset {x // x ∈ sf.ground},
                  sf.sets (t.image Subtype.val) ∧ s = t.image embedding,
    inc_ground := by
      intro s a
      subst h
      simp_all only [Equiv.toFun_as_coe, embedding, toFin, groundFin]
      obtain ⟨w, h⟩ := a
      obtain ⟨_, right⟩ := h
      subst right
      intro x hx
      simp_all only [Finset.mem_image, Subtype.exists, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and]--
      obtain ⟨w_1, h⟩ := hx
      obtain ⟨w_2, h⟩ := h
      obtain ⟨_, right⟩ := h
      subst right
      simp_all only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, exists_prop, exists_eq_right],--
    nonempty_ground := by
      cases sf.nonempty_ground
      rename_i w h_1
      subst h
      simp_all only [Finset.map_nonempty, Finset.attach_nonempty_iff, groundFin]--
      use w
    fintype_ground := Fintype.ofFinset groundFin (by
    intro x
    subst h
    --simp only [Finset.mem_map,  Finset.mem_val]--
    rfl),
  }

-- 補助レマ：image と filter を組み合わせたもの
lemma image_filter_eq {X Y : Type} [DecidableEq Y]
  (embedding : X → Y)
  (tB : Finset X) (B : Finset Y)
  (A : Finset Y)
  (hBmaps : tB.image embedding = B)
  (hAsubset : A ⊆ B) :
  (tB.filter (λ x => embedding x ∈ A)).image embedding = A :=
  by
    -- 任意の y ∈ Y に対して、等式を示すために extensionality を使用
    ext y
    constructor
    -- 第一方向: (LHS) y ∈ (tB.filter (λ x, embedding x ∈ A)).image embedding → y ∈ A
    intro hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    -- x ∈ tB.filter (λ x, embedding x ∈ A) なので、x ∈ tB かつ embedding x ∈ A
    subst hBmaps hxy
    simp_all only [Finset.mem_filter]
    -- 第二方向: y ∈ A → y ∈ (tB.filter (λ x, embedding x ∈ A)).image embedding
    intro hy
    -- A ⊆ tB.image embedding なので、y ∈ tB.image embedding
    have hy_in_B := hAsubset hy
    subst hBmaps
    simp_all only [Finset.mem_image, Finset.mem_filter]
    obtain ⟨w, h⟩ := hy_in_B
    obtain ⟨left, right⟩ := h
    subst right
    exact ⟨w, ⟨left, hy⟩, rfl⟩

omit [Fintype α]  in  --omit [Nonempty α]をつけると他のところでエラー。原因追及する必要あり。
lemma attach_lem (ifmG: Finset α) (tB : Finset { x // x ∈ ifmG }):
   tB = ifmG.attach ↔ Finset.image Subtype.val tB = ifmG := by
  apply Iff.intro
  · -- tB = ifmG.attach → Finset.image Subtype.val tB = ifmG
    intro h
    rw [h]
    exact Finset.attach_image_val
  · -- Finset.image Subtype.val tB = ifmG → tB = ifmG.attach
    intro h

    have lem0: tB ⊆ ifmG.attach := by
      intro x _
      exact Finset.mem_attach _ _

    apply Finset.eq_of_subset_of_card_le lem0

    have lem_leq1: ifmG.attach.card ≤ tB.card := by
      -- `ifmG.attach.card = ifmG.card` を示す

      have h_card_eq : (Finset.image Subtype.val tB).card = tB.card := Finset.card_image_of_injective tB Subtype.val_injective
      rw [←h_card_eq]
      simp_all only [Finset.card_attach, le_refl]

  -- `ifmG.attach.card = tB.card` を導く
    simp_all only [Finset.card_attach]

-- IdealFamily を Fin n 上に変換する関数
noncomputable def toIdealFinFamily (ifm : IdealFamily α) (n : ℕ) (h : Fintype.card ifm.ground = n) : IdealFamily (Fin n) :=
  let sfFin := SetFamily.toFinFamily ifm.toSetFamily n h
  let embedding := (Fintype.equivFinOfCardEq h).toFun -- embedding from SetFamily.toFinFamily
  {
    -- SetFamily のフィールドを継承
    ground := sfFin.ground,
    sets := sfFin.sets,
    inc_ground := sfFin.inc_ground,
    nonempty_ground := sfFin.nonempty_ground,
    fintype_ground := sfFin.fintype_ground,

    -- IdealFamily の追加フィールドを定義
    has_empty := by
      simp_all only [SetFamily.sets, SetFamily.toFinFamily]
      exact ⟨∅, ifm.has_empty, by simp⟩,

    has_ground := by
      simp_all only [SetFamily.sets, SetFamily.toFinFamily]
      exact ⟨ifm.ground.attach, by simp [ifm.has_ground], by
        --goal sfFin.ground = Finset.image (Fintype.equivFinOfCardEq h).toFun ifm.ground.attach
        dsimp [sfFin, SetFamily.toFinFamily]
        simp only [Finset.map, Finset.attach]
        subst h
        simp only [Function.Embedding.coeFn_mk]
        ext1 a
        simp only [Finset.mem_mk, Multiset.mem_map, Multiset.mem_attach, Finset.mem_image]--
      ⟩,

    down_closed := by
      -- 任意の A, B : Finset (Fin n) に対して、
      -- sets B, B ≠ groundFin, A ⊆ B なら sets A を示す
      intros A B hB hBne hAsubset
      -- hB は ∃ tB : Finset {x // x ∈ ifm.ground}, sets (tB.image Subtype.val) ∧ B = tB.image embedding
      obtain ⟨tB, hSetsB, hBmaps⟩ := hB
      -- A ⊆ B = tB.image embedding
      -- tA を {x // embedding x ∈ A} と定義
      have inv: B = tB.image embedding := by --hBmapsそのままかも。逆向きにtBをBで表すのは、難しいかも。
        exact hBmaps

      -- sfFin.ground = ifm.ground これは成り立たない。左はFinset(Fin n)で右はFinset α。
      have invground: ifm.ground.attach.image embedding = sfFin.ground := by
        dsimp [sfFin, SetFamily.toFinFamily]
        simp_all only [ Finset.map, Finset.attach, Fintype.equivFinOfCardEq, embedding]
        simp
        subst h inv
        --simp_all only [ sfFin]
        ext1 a
        simp only [Finset.mem_image, Finset.mem_mk,  Multiset.mem_map]--

      let tA := tB.filter (λ x => embedding x ∈ A)
      -- tA.image embedding = A を証明

      have tA_image_eq : tA.image embedding = A := by
        exact image_filter_eq embedding tB B A hBmaps.symm hAsubset
      -- tA ⊆ tB を証明
      have tA_subset_tB : tA ⊆ tB := Finset.filter_subset _ _
      -- tA.image Subtype.val が ifm.sets に属することを証明
        -- Finset.image_subset_of_subset を用いて tA.image Subtype.val ⊆ tB.image Subtype.val を証明
        -- tA が集合族に属することを証明
      --tBがもともとの集合族でsetsに属していることを利用したい。
      --そもそももともとの集合族でdown_closedが成り立っていることを利用したい。元々の集合族は、ifmである。
      have A_subset_B' : tA.image Subtype.val ⊆ tB.image Subtype.val := by
        subst h hBmaps
        simp only [tA]--
        rw [Finset.image_subset_iff]
        intro x a
        simp_all only [Finset.mem_filter, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
          Finset.coe_mem, exists_const]--

      by_cases h_eq : tB = ifm.ground.attach-- {x // x ∈ ifm.ground}
      -- ケース1: tB = {x // x ∈ ifm.ground}
      -- この場合、B = groundFin となる
      -- しかし、hBne により B ≠ groundFin であるため矛盾が生じる
      case pos =>
        exfalso
        --結論に関係なく、仮定に矛盾がある。使う仮定は、hBneとh_eqのみ。tBが全体集合なので、それに対応するBも全体集合になる。
        subst hBmaps h h_eq
        simp_all only [tA]

      case neg =>
        have hBne_correct : Finset.image Subtype.val tB ≠ ifm.ground := by
        --tBをembeddingしたさきは、全体集合でないということ。h_eqの仮定からこれがいえるはず。ifm groundは、alpha上。
          by_contra h_contra
          --invground: ifm.ground.attach.image embedding = sfFin.ground
          --h_eq ¬tB = ifm.ground.attach
          let result := (attach_lem ifm.ground tB).mpr h_contra
          --#check result -- tB = ifm.ground.attach
          contradiction
          --lemma attach_lem (ifmG: Finset α) (tB : Finset { x // x ∈ ifmG }):
          --tB = ifmG.attach ↔ Finset.image Subtype.val tB = ifmG

        have hSetsA_original : ifm.sets (tA.image Subtype.val) := by
          exact ifm.down_closed (tA.image Subtype.val) (tB.image Subtype.val) hSetsB hBne_correct A_subset_B'

        exact ⟨tA, hSetsA_original, tA_image_eq.symm⟩
  }

  lemma equal_card_fin_ideal_family {n : ℕ} (ifm : IdealFamily α) (h : Fintype.card ifm.ground = n) :
     Fintype.card (@toIdealFinFamily α _ _ ifm n h).ground = n := by
       let sfFin := SetFamily.toFinFamily ifm.toSetFamily n h
       simp only [toIdealFinFamily]
       let toFin : ifm.ground ≃ Fin n := Fintype.equivFinOfCardEq h
       let embedding : {x // x ∈ ifm.ground} → Fin n := toFin.toFun
       have invground: ifm.ground.attach.image embedding = sfFin.ground := by
         dsimp [sfFin, SetFamily.toFinFamily]
         simp_all only [ Finset.map,  embedding]--
         simp
         subst h
         simp_all only [Fintype.card_coe, Finset.one_le_card, toFin]
         ext1 a
         simp only [Finset.mem_image, Finset.mem_mk, Multiset.mem_map]--
         rfl

       --この辺りの補題は使ってないように見えて、コメントアウトするとエラー
       have lem0: ifm.ground.attach.card = n := by
         rw [←h]
         subst h
         simp only [Fintype.card_coe, Finset.card_attach]--

       have inj : Function.Injective embedding := by
           -- `Equiv.injective` を使って単射性を示す
          exact Equiv.injective (Fintype.equivFinOfCardEq h)

       have lem1: ifm.ground.attach.card = (ifm.ground.attach.image embedding).card := by
         exact (Finset.card_image_of_injective ifm.ground.attach inj).symm

       have lem2: ifm.ground.attach.card = sfFin.ground.card := by
         subst h
         simp_all only [sfFin]
       subst h
       simp_all only [Fintype.card_coe, sfFin]--

variable {β : Type} [DecidableEq β]--[DecidableEq α]の方はいらないみたい。βのDecidableは必要。
variable (FSet : Finset (Finset α)) (GSet : Finset (Finset β))
variable (f : α → β)

-- f が A から B への全単射であることを仮定

-- 証明: F と G の要素数は等しい
omit [DecidableEq α] [Fintype α] in --omit [Fintype α] [Fintype β]
theorem same_cardinality (hf : Function.Injective f)(hFG : ∀ (T : Finset β), T ∈ GSet ↔ ∃ (S : Finset α),S ∈ FSet ∧ T = S.image f) :
 FSet.card = GSet.card :=
by
  have this_inj: Function.Injective (Finset.image f) := by
    --#check (@Finset.image_injective α (Finset β) (fun(S:Finset α) => S.image f)) hf
    exact Finset.image_injective hf

  --have : GSet.card = (Finset.image (λ (S:Finset α) => S.image f) FSet).card := by
  have : GSet = (Finset.image (Finset.image f) FSet) := by
    ext y
    constructor
    intro hy
    simp_all only [Finset.mem_image]
    obtain ⟨w, h⟩ := hy
    obtain ⟨left, right⟩ := h
    subst right
    exact ⟨w, left, rfl⟩

    intro a
    simp_all only [Finset.mem_image]
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    subst right
    exact ⟨w, left, rfl⟩

  rw [this]
  subst this
  simp_all only [Finset.mem_image]
  rw [Finset.card_image_of_injective _ this_inj]

omit [DecidableEq α] [Fintype α] in
theorem same_summation (hf : Function.Injective f)(hFG : GSet = FSet.image (λ S => Finset.image f S)) :
  FSet.sum Finset.card = GSet.sum Finset.card:=
by
  -- `i` を `FSet` の各要素 `S` に対してその `Finset.image f S` を対応させる関数と定義します
  let i : (S : Finset α) → S ∈ FSet → Finset β := λ S _ => Finset.image f S

  -- `hi` は `i` の出力が常に `GSet` に含まれることを示します
  have hi : ∀ S (hS : S ∈ FSet), i S hS ∈ GSet := by
    intros S hS
    simp_all only [i]
    subst hFG
    simp_all only [Finset.mem_image]
    exact ⟨S, hS, rfl⟩

  -- `i_inj` は、`i` が `hf` の injectivity により一意であることを示します
  have i_inj : ∀ S₁ (hS₁ : S₁ ∈ FSet) S₂ (hS₂ : S₂ ∈ FSet), i S₁ hS₁ = i S₂ hS₂ → S₁ = S₂ := by
    intros S₁ _ S₂ _ h_eq
    apply Finset.image_injective hf
    exact h_eq

  -- `i_surj` は `i` が `GSet` の任意の要素に対応する `FSet` の元を持つことを示します
  have i_surj : ∀ T ∈ GSet, ∃ S, ∃ (hS : S ∈ FSet), i S hS = T := by
    intros T hT
    subst hFG
    simp_all only [Finset.mem_image, exists_prop, i]

  -- 各 `S ∈ FSet` に対して `Finset.card S = Finset.card (Finset.image f S)` であることを示します
  have h : ∀ S (hS : S ∈ FSet), Finset.card S = Finset.card (i S hS) := by
    intros S hS
    rw [Finset.card_image_of_injective _ hf]

  -- `Finset.sum_bij` を適用して `FSet` の合計と `GSet` の合計が等しいことを示します
  exact Finset.sum_bij i hi i_inj i_surj h

end Ideal
