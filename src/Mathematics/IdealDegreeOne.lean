import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Mathlib.Init.Function
import Mathlib.Init.Logic
import Mathematics.BasicDefinitions
import Mathematics.BasicLemmas
import Mathematics.IdealTrace
import LeanCopilot

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

namespace Mathematics

def hasDegreeOneSetFamily (F : SetFamily α) : Prop :=
  ∃ (v : α), degree F v = 1

--次数が1の点をtraceをすると標準化次数和が下がること。
--theorem trace_does_not_decrease_normalized_degree_sum {α : Type} [DecidableEq α] [Fintype α]
--  (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2) (deg1: degree F x = 1) :
--  (normalized_degree_sum (IdealTrace.trace F x hx gcard)) ≥ normalized_degree_sum F :=
--  by

--補題をノーヒントで自動で出してもらったがろくなものがないかも。人間があらすじを書いて補題を作ってもらう必要がある。

--xでtraceするとその集合族にはxが含まれないこと。別のところで証明されている可能性あり。
--lemma trace_sets_property {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2) :
--  ∀ (s :Finset α ),(IdealTrace.trace F x hx gcard).sets s → x ∉ s :=
--  by
--    sorry

--degreeの定義を書き写しただけか。簡単に証明できたので証明しておいた。使わないかも。
lemma degree_calculation {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x : α) :
  degree F x = (Finset.filter (λ s => F.sets s ∧ x ∈ s) (all_subsets F.ground)).card :=
  by
    simp_all only [degree, all_subsets, Finset.card_filter]
    simp [Finset.filter]

--vの次数が1であれば、全体集合以外のhyperedgeは、vを通らない。
lemma hyperedges_not_through_v {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground) :
  ∀ s, F.sets s → s ≠ F.ground → v ∉ s :=
 by
  intros ss hs hneq
  by_contra h
  have h_deg1 := deg1
  unfold degree at h_deg1
  rw [Finset.card_eq_one] at h_deg1
  obtain ⟨t, ht⟩ := h_deg1
  -- Finset.filter (fun s ↦ F.sets s = (true = true) ∧ v ∈ s) (all_subsets F.ground) = {t}
  apply hneq
  have set2inc1: F.ground ∈ (Finset.filter (fun s ↦ F.sets s = true ∧ v ∈ s) (all_subsets F.ground)):= by
    simp
    rw [all_subsets]
    constructor
    simp
    exact ⟨hasGround, hv⟩
  have set2inc2: ss ∈ (Finset.filter (fun s ↦ F.sets s = true ∧ v ∈ s) (all_subsets F.ground)):= by
    simp
    constructor
    have ssground: ss ⊆ F.ground := by
      exact F.inc_ground ss hs
    --unfold SetFamily.sets at hs
    simp_all
    rw [all_subsets]
    --rw [Finset.powerset]
    exact Finset.mem_powerset.mpr ssground
    constructor
    exact hs
    exact h

  have set2card: ({F.ground, ss}:Finset (Finset α) ).card = 2 := by
    rw [Finset.card_insert_of_not_mem]
    simp [hneq]
    by_contra
    simp_all
  let degset := Finset.filter (fun s ↦ F.sets s = true ∧ v ∈ s) (all_subsets F.ground)
  have set2card2:  ({F.ground, ss}:Finset (Finset α) ) ⊆ degset := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    cases hz with
    | inl hzx => rw [hzx]; exact set2inc1
    | inr hzy => rw [hzy]; exact set2inc2

  have set2card3: 2 ≤ degset.card := by
    rw [←set2card]
    exact Finset.card_le_card set2card2

  have deg2: degree F v >= 2 := by
    -- v ∈ F.ground かつ sets F.ground で、v ∈ sかつsets s で、s ≠ F.ground なので、degreeは2以上になる。
    dsimp [degree]
    simp [set2card3]
    simpa [degset] using set2card3
  rw [deg1 ] at deg2
  contradiction

--次数が1である性質でいえること。本来は、次数が1なので、全体集合以外は、traceしてもhyperedgeの数も大きさもかわらないことを証明すればよい。
--lemma degree_one_property {α : Type} [DecidableEq α] [Fintype α]
--  (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (deg1: degree F x = 1) :
--  ∃ s, s ∈ F.sets ∧ x ∈ s ∧ ∀ t ∈ F.sets, x ∈ t → t = s :=
--def trace {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2):
-- (hnot: ¬ F.sets (F.ground.erase v)) の仮定は証明に使わ下なったので、消した。
lemma trace_hyperedge_equiv {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground)(gcard: F.ground.card ≥ 2) :
  {s : Finset α|(IdealTrace.trace F v hv gcard).sets s} = { s : Finset α|F.sets s ∧ s ≠ F.ground } ∪ { F.ground.erase v } :=
by
  ext s
  simp only [IdealTrace.trace, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro h --v ∉ s ∧ (F.sets s ∨ F.sets (s ∪ {v}))
    --have hcopy: (IdealTrace.trace F v hv gcard).sets s := h
    have h2 := h.2
    have h1 := h.1
    show (F.sets s ∧ s ≠ F.ground) ∨ (s = F.ground.erase v)
    cases h2 with
    | inl hs =>
      --goal F.sets s ∧ s ≠ F.ground
      --hs: F.sets s
      --h.1: v ∉ s
      --hv: v ∈ F.ground
      have snfg: s ≠ F.ground := by
        intro hfg
        rw [hfg] at hs -- hs F.sets: F.ground なので、矛盾
        rw [hfg] at h1 -- h1: v ∉ F.ground なので、矛盾
        contradiction
      left
      exact ⟨hs, snfg⟩
    | inr hs => --F.sets (s ∪ {v})の場合、でもFの集合でvを含むものは全体集合のみなので、s = F.ground.erase v になる。
      --simp_all only [ge_iff_le, Set.mem_singleton_iff]
      --goal s = F.ground.erase v
      right
      ext x
      simp only [Finset.mem_erase, Finset.mem_singleton]
      --goal x ∈ s ↔ ¬x = v ∧ x ∈ F.ground
      constructor
      · intro hh -- x ∈ s
          -- goal ¬x = v ∧ x ∈ F.ground
          -- v ∉  s かつ x ∈ s なので、x = v でない。
        have sg: s ∪ {v} ⊆ F.ground := by
            exact F.inc_ground (s ∪ {v}) hs
        constructor
        · intro hnot
          rw [hnot] at hh
          contradiction
        · --show (F.sets s ∧ s ≠ F.ground) ∨ s = F.ground.erase v
            --goal x ¥in F.ground
            -- hh: x ∈ s
            -- sg: s ∪ {v} ⊆ F.ground
            have sg2: s ⊆ F.ground := by
              rename_i α_1 _ _ _ inst_3 inst_4
              simp_all only [not_false_eq_true, or_true, and_self]
              intro y hy
              exact sg (s.subset_union_left hy)

            have hxFg: x ∈ F.ground := by
              exact sg2 hh
            exact hxFg
      · --#check (s ∪ {v})
        intro hh --  ¬x = v ∧ x ∈ F.ground
          --s = F.ground.erase v を示すhaveのなか。
          -- goal x ∈ sがこのintro部分の目標。
          --hyperedges_not_through_vを使って証明する。
          --hyperedges_not_through_v {α : Type} [DecidableEq α] [Fintype α]
          --(F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground) :
          -- ∀ s, F.sets s → s ≠ F.ground → v ∉ s
          -- hs : F.sets (s ∪ {v})を利用する。
        by_cases sfground: (s ∪ {v}) = F.ground
        case pos =>
            -- sfground : s ∪ {v} = F.ground
            -- hh: ¬x = v ∧ x ∈ F.ground
            --からいえる。
          cases hh with
          |intro hne hFground =>
          have xsv:x ∈ s ∪ {v} := sfground.symm ▸ hFground
          rw [Finset.mem_union] at xsv
          cases xsv with
          | inl hxs => exact hxs
          | inr hxv =>
            rw [Finset.mem_singleton] at hxv
            contradiction

        case neg =>
          let result := hyperedges_not_through_v F v hv deg1 hasGround (s ∪ {v}) hs sfground
          have vdv: v ∈ s ∪ {v} := by
            simp
          contradiction
        -- ここまでで全体の補題の片方行が終わった。
  · intro h
    --h : ({s | F.sets s ∧ s ≠ F.ground} ∪ {F.ground.erase v}) s
    -- hを (F.sets s ∧ s ≠ F.ground) ∨ (s = F.ground.erase v)
    --goal  v ∉ s ∧ (F.sets s ∨ F.sets (s ∪ {v}))
    constructor
    --goal v ∉ s
    cases h with
    | inl hset =>
      have hneq := hset.2
      let result := hyperedges_not_through_v F v hv deg1 hasGround s hset.1 hneq
      exact result
    | inr hset =>
      have hset2 : s = F.ground.erase v  := hset
      rw [hset2]
      simp

    --goal F.sets s ∨ F.sets (s ∪ {v})
    -- h: (F.sets s ∧ s ≠ F.ground) ∨ s ∈ {F.ground.erase v}
    cases h with
    | inl h1 => left;exact h1.1
    | inr h2 => --s ∈ {F.ground.erase v}
      right
      -- h2: s = F.ground.erase v
      --hasGround : F.sets F.ground でこれを変換したものが
      -- hnot: ¬ F.sets (F.ground.erase v)と矛盾
      let fgsv := F.ground.erase v
      have fgsv2: fgsv = F.ground.erase v := by rfl
      rw [←fgsv2] at h2
      have ss: s = fgsv := by
        exact h2
      dsimp [fgsv] at ss
      --s = F.ground.erase v
      have ground2: s ∪ {v} = F.ground := by
        rw [ss]
        --F.ground.erase v ∪ {v} = F.ground
        exact erase_insert F.ground v hv
      rw [ground2]
      exact hasGround

end Mathematics
