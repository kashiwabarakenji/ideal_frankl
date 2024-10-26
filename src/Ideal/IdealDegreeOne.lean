import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
--import Mathlib.Init.Function
import Mathlib.Init.Logic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import Ideal.IdealTrace
import Ideal.IdealSimple
import LeanCopilot

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

namespace Ideal

def hasDegreeOneSetFamily (F : SetFamily α) : Prop :=
  ∃ (v : α), degree F v = 1

--vの次数が1であれば、全体集合以外のhyperedgeは、vを通らない。IdealSimple.leanでも同様なことを証明。
--このファイルの他の部分で何回か利用。
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
  have set2inc1: F.ground ∈ (Finset.filter (fun s ↦ F.sets s = true ∧ v ∈ s) (F.ground.powerset)):= by
    simp
    constructor
    simp_all only [ne_eq, eq_iff_iff, iff_true]
    simp_all only [ne_eq, eq_iff_iff, iff_true]
    --exact ⟨hasGround, hv⟩
  have set2inc2: ss ∈ (Finset.filter (fun s ↦ F.sets s = true ∧ v ∈ s) (F.ground.powerset)):= by
    simp
    constructor
    have ssground: ss ⊆ F.ground := by
      exact F.inc_ground ss hs
    simp_all
    simp_all only [ne_eq, eq_iff_iff, iff_true, Finset.mem_singleton, and_self]


  have set2card: ({F.ground, ss}:Finset (Finset α) ).card = 2 := by
    rw [Finset.card_insert_of_not_mem]
    simp [hneq]
    by_contra
    simp_all
  let degset := Finset.filter (fun s ↦ F.sets s = true ∧ v ∈ s) (F.ground.powerset)
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
--IdealTraceに移動してもいいが、deg1の仮定が必要なので、ここに置いておく。補題の名前もdegoneの仮定を反映しても良い。
--lemma degree_one_property {α : Type} [DecidableEq α] [Fintype α]
--  (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (deg1: degree F x = 1) :
--  ∃ s, s ∈ F.sets ∧ x ∈ s ∧ ∀ t ∈ F.sets, x ∈ t → t = s :=
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
              --rename_i α_1 _ _ _ inst_3 inst_4
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



lemma total_degone_card {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground)(gcard: F.ground.card ≥ 2) :
  total_size_of_hyperedges F = (F.ground.powerset.filter (λ s => F.sets s ∧ v ∉ s )).sum Finset.card + F.ground.card := by
  rw [total_size_of_hyperedges]
  simp
  --使わなかった。dis_lem
  --have _: Disjoint (Finset.filter (λ s => F.sets s ∧ v ∉ s ) (F.ground.powerset)) ({F.ground}) := by
  --  simp_all only [ne_eq, Set.union_singleton, Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_powerset,
  --    subset_refl, not_true_eq_false, and_false, not_false_eq_true]
  have union_lem:Finset.filter (λ s => F.sets s ∧ v ∉ s ) (F.ground.powerset) ∪ {F.ground} = Finset.filter (λ s => F.sets s) (F.ground.powerset) := by
    ext1 a
    simp_all only [ne_eq, Set.union_singleton, Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_powerset,
      subset_refl, not_true_eq_false, and_false, not_false_eq_true, Finset.card_union_of_disjoint, Finset.card_singleton]
    apply Iff.intro
    intro a_1
    simp_all only [ge_iff_le, Finset.mem_union, Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    cases a_1 with
    | inl h => simp_all only [and_self]
    | inr h_1 =>
      subst h_1
      simp_all only [subset_refl, and_self]
    intro a_1
    simp_all only [ge_iff_le, Finset.mem_union, Finset.mem_filter, Finset.mem_powerset, true_and,
      Finset.mem_singleton]
    obtain ⟨_, right⟩ := a_1
    let assum := (hyperedges_not_through_v F v hv deg1 hasGround) a right
    simp at assum
    tauto

  have card_sum: (Finset.filter (λ s => F.sets s) (F.ground.powerset)).sum Finset.card = (Finset.filter (λ s => F.sets s ∧ v ∉ s ) (F.ground.powerset)).sum Finset.card + F.ground.card := by
    simp_all only [ge_iff_le, Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_powerset, subset_refl,
    not_true_eq_false, and_false, not_false_eq_true]
    symm
    rw [← union_lem, Finset.sum_union]
    · simp_all only [Finset.sum_singleton]
    · simp_all only [Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_powerset, subset_refl,
      not_true_eq_false, and_false, not_false_eq_true]

  simp_all only [ge_iff_le, Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_powerset, subset_refl,
    not_true_eq_false, and_false, not_false_eq_true]

lemma ground_minus_v_ideal_sets {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) (v : α) (hv: v ∈ F.ground) (hv_singleton:  ¬F.sets {v}) (hv_hyperedge:F.sets (F.ground \ {v})):
  ∀ s ∈ F.ground.powerset, F.sets s ↔ v ∉ s ∨ s = F.ground := by
        have degree_one: degree F.toSetFamily v = 1 := by
            exact degree_one_if_not_hyperedge F hv hv_singleton
        intro s hs
        simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset]
        apply Iff.intro
        · intro a
          let ground_assum := (hyperedges_not_through_v F.toSetFamily v hv degree_one F.univ_mem) s a
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

lemma ground_minus_v_ideal_number {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) (v : α) (hv: v ∈ F.ground)  (hv_hyperedge:F.sets (F.ground \ {v}))(hv_singleton:  ¬F.sets {v}):
    number_of_hyperedges F.toSetFamily = 2^(F.ground.card - 1) + 1 :=
    by
      rw [Ideal.number_of_hyperedges]

        -- `v` を含まない部分集合を取り出す
      let A := Finset.filter (λ s=> v ∉ s) F.ground.powerset
      -- `s = F.ground` を満たす唯一の部分集合を取り出す
      let B : Finset (Finset α) := {F.ground}

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
          apply Finset.ext
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
          simp_all only [true_and]
          obtain ⟨left, right⟩ := h
          have slem: s ⊆ F.ground.erase v := by
            intro x hx
            simp_all only [Finset.mem_erase, ne_eq]
            apply And.intro
            · apply Aesop.BuiltinRules.not_intro
              intro a
              subst a
              simp_all only
            · exact left hx
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
          exact F.down_closed s (F.ground.erase v) FsetG hsng slem

          constructor
          rename_i h
          subst h
          simp_all only [Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_powerset, subset_refl,
            not_true_eq_false, and_false, not_false_eq_true, A, B]

          rename_i h
          subst h
          simp_all only [Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_powerset, subset_refl,
            not_true_eq_false, and_false, not_false_eq_true, A, B]
          exact F.univ_mem
          -- F.sets に属する場合
          intro hs
          simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff,
            Finset.mem_singleton, not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false,
            not_false_eq_true, sdiff_eq_left, Finset.disjoint_singleton_right, or_false, Finset.mem_filter,
            subset_refl, true_and, A, B]
          obtain ⟨left, right⟩ := hs
          have left0: s ∈ F.ground.powerset := by
            simp_all only [Finset.mem_powerset]
          exact (ground_minus_v_ideal_sets F v hv hv_singleton hv_hyperedge s left0).mp right

      -- `A` のカードは `2 ^ (F.ground.card - 1)` であることを示す
      have h_A_card : A.card = 2 ^ (F.ground.card - 1) :=
        by
          dsimp [A]

          have sub_lem: ∀ s :Finset α,s ∈ (Finset.filter (fun s => v ∉ s) F.ground.powerset) ↔ s ⊆ F.ground.erase v := by
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
              exact Finset.subset_erase.mp h

          have sub_lem2: (Finset.filter (fun s => v ∉ s) F.ground.powerset).card = (Finset.filter (fun s => s ⊆ F.ground.erase v) F.ground.powerset).card := by
            simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff,
                Finset.mem_singleton, not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false,
                not_false_eq_true, sdiff_eq_left, Finset.disjoint_singleton_right, or_false, Finset.mem_filter, A, B]
            apply Finset.card_bij (fun s _ => s)

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
          have h_card : (F.ground.erase v).card = F.ground.card - 1 := Finset.card_erase_of_mem hv
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


lemma powerset_bij {α : Type} [DecidableEq α][Fintype α]  (FG : Finset α) (a : α) (h : a ∈ FG) :
  (FG.powerset.filter (fun S => a ∈ S)).card = (FG.erase a).powerset.card := by

    -- 2. 対象となる Finset を定義します。
  let ss := FG.powerset.filter (fun S => a ∈ S)  -- Finset (Finset α)
  let tt := (FG.erase a).powerset                 -- Finset (Finset α)
  let i := fun (S : Finset α) (_ : S ∈ ss) => S.erase a
  -- `Finset.card_bij` を使って証明する
  --#check Finset.card_bij
  apply @Finset.card_bij (Finset α) (Finset α) ss tt i
    -- 対応関数: `S` に対して `S.erase a`

    -- `S.erase a` が `FG.erase a` の部分集合に含まれることを示す
    -- 3.1. hi の証明: ∀ S ∈ ss, i S hS ∈ tt
    (by
      intro S hS
      --simp_all only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase]
      simp_all only [Finset.mem_powerset, i, ss, tt]
      simp_all only [Finset.mem_filter, Finset.mem_powerset, ss]
      obtain ⟨left, _⟩ := hS
      intro x hx
      simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
      obtain ⟨_, right_1⟩ := hx
      exact left right_1
    )

    --  λ S hS => Finset.mem_erase.mp (Finset.mem_filter.mp hS).2)
    --(λ S hS => Finset.erase_subset hS h)
    -- 単射性の証明
    (λ S₁ hS₁ S₂ hS₂ h_eq=> by {
      simp_all only [Finset.mem_powerset, i, ss, tt]
      simp_all only [Finset.mem_filter, Finset.mem_powerset, ss]
      obtain ⟨_, right₁⟩ := hS₁
      obtain ⟨_, right₂⟩ := hS₂
      have eq_goal: S₁ = S₂ := by
        ext x_1
        apply Iff.intro
        · intro a_1
          by_cases h : x_1 = a
          · rw [h]
            simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
          · have h_tmp: x_1 ∈ S₁.erase a:= by
              rw [Finset.mem_erase]
              exact ⟨h ,a_1⟩
            simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
        · intro a_1
          by_cases h : x_1 = a
          · rw [h]
            simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
          · have h_tmp2: x_1 ∈ S₂.erase a:= by
              rw [Finset.mem_erase]
              exact ⟨h ,a_1⟩
            rw [←h_eq] at h_tmp2
            rw [Finset.mem_erase] at h_tmp2
            exact h_tmp2.2
      exact eq_goal
    })
    -- 全射性の証明
    (by
      intro T hT
      have goal: ∃ a, ∃ (ha : a ∈ ss), i a ha = T := by
        use insert a T
        dsimp [tt] at hT
        simp_all only [Finset.mem_powerset, i, ss, tt]
        rw [Finset.subset_erase] at hT
        have tmp_goal: insert a T ⊆ FG:= by
          obtain ⟨left, _⟩ := hT
          rw [Finset.insert_subset_iff]
          simp_all only [and_self]
        have tmp_goal2: a ∈ insert a T := by
          simp_all only [Finset.mem_insert_self]
        use Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr tmp_goal, tmp_goal2⟩
        --  error hT has type  T ∈ tt : Prop but is expected to have type insert a T ⊆ FG : Prop


        simp_all only [Finset.mem_insert_self, Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
        simp_all only [Finset.erase_insert_eq_erase, not_false_eq_true, Finset.erase_eq_of_not_mem]
      exact goal
    )

--下で利用する補題。
-- 任意の要素 a ∈ FG に対して、a を含む部分集合の数は 2^(n-1) である
lemma count_subsets_containing_a {α : Type} [DecidableEq α][Fintype α]
  (FG : Finset α) (n : ℕ) (h_n : FG.card = n) (a : α) (ha : a ∈ FG) :
  (FG.powerset.filter (fun S => a ∈ S)).card = 2 ^ (n - 1) := by

  have h_erase_card : (FG.erase a).card = n - 1 := by
    rw [Finset.card_erase_of_mem ha]
    subst h_n
    simp_all only

  have h_powerset_eq : (FG.powerset.filter (fun S => a ∈ S)).card = (FG.erase a).powerset.card := by
    exact (powerset_bij FG a ha)

  have finset_card_powerset_filter_eq_powerset_erase : (FG.powerset.filter (fun S => a ∈ S)).card = (FG.erase a).powerset.card :=
    by
      exact h_powerset_eq

  have h_powerset_erase_card : (FG.erase a).powerset.card = 2 ^ (n - 1) := by
    rw [Finset.card_powerset]
    rw [h_erase_card]

  rw [finset_card_powerset_filter_eq_powerset_erase]
  rw [h_powerset_erase_card]

-- 和の数える順番の補題。
lemma sum_card_powerset_eq_sum_subsets_containing {α : Type} [DecidableEq α] [Fintype α] {FG : Finset α} :
  FG.powerset.sum (λ s => ∑ a ∈ s, 1) = FG.sum (λ a => (FG.powerset.filter (λ S => a ∈ S)).card) :=
by
  let fn (a : α) (s : Finset α): Nat := if a ∈ s then 1 else 0
  -- 左辺を展開して、card s を ∑ a ∈ s, 1 と等しくする

  have rewrite : ∑ a ∈ FG, (Finset.filter (fun S => a ∈ S) FG.powerset).card = ∑ a ∈ FG, ∑ x ∈ (Finset.filter (fun S => a ∈ S) FG.powerset), 1 := by
    simp_all only [Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_boole, Nat.cast_id]
  rw [rewrite]

  have rewrite2 : ∑ a ∈ FG, ∑ x ∈ (Finset.filter (fun S => a ∈ S) FG.powerset), 1 = ∑ a ∈ FG, ∑ x ∈ FG.powerset, fn a x := by
    simp_all only [Finset.sum_const, smul_eq_mul, mul_one]
    have rewrite3:  ∀ a, ∑ x ∈ (Finset.filter (fun S => a ∈ S) FG.powerset), 1 = ∑ x ∈ FG.powerset, fn a x := by
       intro a
       simp [Finset.sum_congr rfl]
       dsimp [fn]
       simp
    congr
    ext a : 2
    simp_all

  rw [rewrite2]

  have rewrite4: ∑ s ∈ FG.powerset, ∑ a ∈ s, 1 = ∑ s ∈ FG.powerset, ∑ a ∈ FG, fn a s := by
    dsimp [fn]
    apply Finset.sum_congr
    rfl
    intro x a
    simp_all only [Finset.sum_const, smul_eq_mul, mul_one, Finset.mem_powerset, Finset.sum_ite_mem]
    congr
    exact (Finset.inter_eq_right.mpr a).symm

  rw [rewrite4]

  -- 和の順序を入れ替える
  rw [Finset.sum_comm]

--lemma sum_filter_card_eq {α : Type} [DecidableEq α][Fintype α]  (FG : Finset α) (a : α) :
--  (FG.powerset.filter (λ S => a ∈ S)).sum (λ S => 1) = (FG.powerset.filter (λ S => a ∈ S)).card :=
--by
--  simp_all

-- 主定理: FG.powerset.sum Finset.card = FG.card * 2 ^ (FG.card - 1)
theorem powerset_sum_card_eq_card_mul_pow {α : Type} [DecidableEq α][Fintype α]
  (FG : Finset α)
  (h_nonempty : FG.card ≥ 1) :
  FG.powerset.sum Finset.card = FG.card * 2 ^ (FG.card - 1) := by
  -- 証明のために n を FG.card と定義
  let n := FG.card
  -- n が 1 以上であることを確認
  have h_n : n ≥ 1 := h_nonempty

  -- 補題2: 冪集合のカードの合計を、各要素が含まれる部分集合の数の合計に置き換える
  have sum_eq_sum : FG.powerset.sum Finset.card = (FG.sum (fun a => (FG.powerset.filter (fun S => a ∈ S)).card)) := by
    --∑ s ∈ FG.powerset, ∑ a ∈ s, 1 = ∑ a ∈ FG, (filter (fun S => a ∈ S) FG.powerset).card
    have left_hand_side : FG.powerset.sum Finset.card = ∑ s ∈ FG.powerset, ∑ a ∈ s, 1:= by
      simp_all only [Finset.sum_const, smul_eq_mul, mul_one]
    have right_hand_side : FG.sum (fun a => (FG.powerset.filter (fun S => a ∈ S)).card) = ∑ a ∈ FG, (Finset.filter (fun S => a ∈ S) FG.powerset).card := by
      simp_all only [ge_iff_le, Finset.one_le_card, Finset.sum_const, smul_eq_mul, mul_one, n]
    rw [left_hand_side, right_hand_side]
    simp_all
    --#check sum_card_powerset_eq_sum_subsets_containing
    let scp := @sum_card_powerset_eq_sum_subsets_containing _ _ _ FG

    -- ∑ s ∈ FG.powerset, ∑ a ∈ s, 1 = ∑ a ∈ FG, (filter (fun S => a ∈ S) FG.powerset).card
    --#check card_eq_sum_ones2
    simp [Fintype.card_eq_sum_ones] at scp
    --goal ∑ x ∈ FG.powerset, x.card = ∑ a ∈ FG, (filter (fun S => a ∈ S) FG.powerset).card
    convert sum_card_powerset_eq_sum_subsets_containing
    simp_all only [Finset.one_le_card, Finset.mem_powerset, Finset.sum_const, smul_eq_mul, mul_one, n]
    rename_i inst_1
    simp_all only [Finset.one_le_card, n]
    exact inst_1
    --強引に解決。

  -- 各要素 a ∈ FG に対して、a を含む部分集合の数は 2^(n-1) であることを補題1で示す
  have sum_contrib : FG.sum (fun a => (FG.powerset.filter (fun S => a ∈ S)).card) = FG.card * 2 ^ (n - 1) := by
    -- 各 a ∈ FG に対して補題1を適用
    rw [Finset.sum_congr rfl (fun a ha => by
      -- 補題1を適用
      rw [count_subsets_containing_a FG n rfl a ha]
    )]
    -- 定数の和を計算
    rw [Finset.sum_const, mul_comm]
    simp_all only [ge_iff_le, Finset.one_le_card, smul_eq_mul, n]
    ring

  -- 補題2と補題1の結果を組み合わせる
  rw [sum_eq_sum, sum_contrib]

lemma ground_minus_v_ideal_total {α : Type} [DecidableEq α] [Fintype α] (F : IdealFamily α) (v : α) (hv: v ∈ F.ground)  (hv_hyperedge:F.sets (F.ground \ {v}))(hv_singleton:  ¬F.sets {v})(hcard0: F.ground.card >= 2):
  total_size_of_hyperedges F.toSetFamily = (F.ground.card - 1)*2^(F.ground.card - 2) + F.ground.card := by
        have degree_one: degree F.toSetFamily v = 1 := by
            exact degree_one_if_not_hyperedge F hv hv_singleton
        rw [Ideal.total_degone_card F.toSetFamily v hv degree_one F.univ_mem hcard0]
        simp_all only [ge_iff_le, Nat.reduceLeDiff, Finset.mem_powerset, Finset.singleton_subset_iff, Finset.mem_singleton,
         not_true_eq_false, false_or, Finset.sdiff_subset, Finset.mem_sdiff, and_false, not_false_eq_true, sdiff_eq_left,
         Finset.disjoint_singleton_right, or_false, add_tsub_cancel_right, Nat.reduceSubDiff, add_left_inj]
        --goal (Finset.filter (fun s => F.sets s ∧ v ∉ s) F.ground.powerset).sum Finset.card = n * 2 ^ (n - 1)
        let A := Finset.filter (λ s=> v ∉ s) F.ground.powerset
        -- `s = F.ground` を満たす唯一の部分集合を取り出す
        let B : (Finset (Finset α)) := {F.ground}
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
            obtain ⟨_, right⟩ := right
            --simp_all only [not_false_eq_true, true_or]
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
              rw [←Finset.mem_powerset] at hxg
              let Fsets:= ground_minus_v_ideal_sets F v hv hv_singleton hv_hyperedge
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
            --rw [Finset.sum_powersetCard]
            have f_geq: (F.ground.erase v).card >= 1 := by
              rw [Finset.card_erase_of_mem hv]
              simp_all only [ge_iff_le]
              omega
            exact powerset_sum_card_eq_card_mul_pow (F.ground.erase v) f_geq
        rw [formula]
        simp_all only [Finset.card_erase_of_mem, mul_eq_mul_left_iff, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one,
          not_false_eq_true, pow_right_inj]
        apply Or.inl
        rfl

--下で利用
lemma degree_one_singleton {α : Type} [DecidableEq α] [Fintype α] (F: IdealFamily α) (v : α) (hv: v ∈ F.ground)(hcard0: F.ground.card >= 2):
  degree F.toSetFamily v = 1 ↔ ¬F.sets {v} := by
    apply Iff.intro
     -- degree F v = 1 → ¬F.sets {v}
    · intro h
      intro a
      --hv: v ∈ F.ground
      --F.univ_mem:F.sets F.ground
      have v_self: v ∈ ({v} : Finset α) := by
        simp_all only [Finset.mem_singleton]
      -- a:F.sets {v}
      have hcard_s: ({v} : Finset α).card = 1 := by
        simp_all only [Finset.card_singleton]
      have neqv: {v} ≠ F.ground := by
        intro hh
        rw [hh] at hcard_s
        rw [hcard_s] at hcard0
        linarith

      have v_filtered: {v} ∈ F.ground.powerset.filter (λ (s:Finset α) => (F.sets s ∧ v ∈ s)) := by
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        simp
        exact hv
      have g_filtered: F.ground ∈ F.ground.powerset.filter (λ (s:Finset α) => (F.sets s ∧ v ∈ s)) := by
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        simp
        exact F.univ_mem

      have lem_subset: (insert ({v}:Finset α) (singleton F.ground)) ⊆ F.ground.powerset.filter (λ (s:Finset α) => (F.sets s ∧ v ∈ s))  := by
        simp_all only [Finset.subset_iff, Finset.mem_singleton, Finset.mem_filter, Finset.mem_powerset]
        intro s
        intro hs
        constructor
        · intro x1
          intro a_1
          simp_all only [ge_iff_le, eq_iff_iff, iff_true, Finset.card_singleton, ne_eq, implies_true, and_self, and_true,
            true_and, Finset.mem_insert, Finset.mem_singleton]
          cases hs
          case inl h_1 =>
            subst h_1
            simp_all only [Finset.mem_singleton]
          case inr h_2 =>
            subst h_2
            simp_all only
        · simp_all only [ge_iff_le, eq_iff_iff, iff_true, Finset.card_singleton, ne_eq, implies_true, and_self, and_true,
            true_and, Finset.mem_insert,Finset.mem_singleton]
          cases hs with
          | inl h_1 =>
            subst h_1
            simp_all only [Finset.mem_singleton, and_self]
          | inr h_2 =>
            subst h_2
            simp_all only [and_self]

      have hcard2: ((insert ({v}:Finset α) (singleton F.ground)):Finset (Finset α)).card = 2 := by
        simp_all only [Finset.card_insert_of_not_mem, Finset.card_singleton]
        simp_all only [ge_iff_le, eq_iff_iff, iff_true, Finset.mem_singleton, ne_eq, Finset.mem_filter, Finset.mem_powerset,
          Finset.singleton_subset_iff, and_self, subset_refl, and_true, true_and, not_false_eq_true, Finset.card_insert_of_not_mem,
          Finset.card_singleton, Nat.reduceAdd]

      --#check (F.ground.powerset.filter (λ (s:Finset α) => (F.sets s ∧ v ∈ s))).card
      have card_le0: ((insert ({v}:Finset α) (singleton F.ground)):Finset (Finset α)).card ≤ (F.ground.powerset.filter (λ (s:Finset α) => (F.sets s ∧ v ∈ s))).card := by
        --rw [hcard2]
        exact Finset.card_le_card lem_subset

      have card_le1: (F.ground.powerset.filter (λ (s:Finset α) => (F.sets s ∧ v ∈ s))).card >= 2 := by
        rw [←hcard2]
        exact card_le0

      have card_le2: degree F.toSetFamily v >= 2 := by
        dsimp [degree]
        simp_all only [ge_iff_le, eq_iff_iff, iff_true, Finset.card_singleton, ne_eq, implies_true, and_self, and_true,
          true_and, Finset.mem_insert, Finset.mem_singleton]

      rw [h] at card_le2
      linarith
    · intro fs
      --IdealSimpleのdegree_one_if_not_hyperedge で証明済みだった。
      -- hの仮定より全体集合以外にもvを含むhyperedgeがある。down_closedを使って、F.sets {v}が得られる。
      exact degree_one_if_not_hyperedge F hv fs

lemma degree_one_ground {α : Type} [DecidableEq α] [Fintype α] (F: IdealFamily α) (v : α) (hv: v ∈ F.ground)(hcard0: F.ground.card >= 2):
  degree F.toSetFamily v = 1 → ∀ (s:Finset α), F.sets s → v ∈ s → s = F.ground := by
    intro h
    intro s
    intro fs
    intro vs
    have h2: ¬F.sets {v} := by
      exact (degree_one_singleton F v hv hcard0).mp h
    by_contra h3
    have v_sub_s: {v} ⊆ s := by
      simp_all only [Finset.singleton_subset_iff, Finset.mem_singleton]
    have h4: F.sets {v} := by
      exact F.down_closed {v} s fs h3 v_sub_s
    exact h2 h4

--(v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground)(gcard: F.ground.card ≥ 2)
lemma filter_sum {α : Type} [DecidableEq α] [Fintype α] (P Q : Finset α → Prop) [DecidablePred P] [DecidablePred Q] (S : Finset (Finset α))  :
  (∀ (s:Finset α), s ∈ S → ¬(P s ∧ Q s)) →
    (Finset.filter (λ (s : Finset α) => P s ∨ Q s) S).sum Finset.card
   = ((Finset.filter (λ (s : Finset α) => P s) S).sum Finset.card) +
    (Finset.filter (λ (s : Finset α) => Q s) S).sum Finset.card := by
    intro disj
    set domain := (Finset.filter (λ (s : Finset α) => P s ∨ Q s) S)
    set rangeP := (Finset.filter (λ (s : Finset α) => P s) S)
    set rangeQ := (Finset.filter (λ (s : Finset α) => Q s) S)
    have d_union:domain = rangeP ∪ rangeQ := by
      apply Finset.ext
      intro x
      constructor
      intro a
      simp_all only [not_and, Finset.mem_filter, Finset.mem_union, true_and, domain, rangeP, rangeQ]
      intro a
      simp_all only [not_and, Finset.mem_union, Finset.mem_filter, rangeP, rangeQ, domain]
      cases a with
      | inl h => simp_all only [or_false, and_self]
      | inr h_1 => simp_all only [or_true, and_self]
    have disjoint: rangeP ∩ rangeQ = ∅ := by
      apply Finset.eq_empty_of_forall_not_mem
      intro x
      simp_all only [Finset.mem_inter, Finset.mem_filter]
      intro h
      obtain ⟨hP, hQ⟩ := h
      simp_all only [not_and, Finset.mem_filter, and_false, rangeP, rangeQ]
    have disjoint0: Disjoint rangeP rangeQ := by
      dsimp [Disjoint]
      intro x
      intro xrp xrq
      have xsub: x ⊆ rangeP ∩ rangeQ := by
        --simp_all only [Finset.mem_inter, Finset.mem_filter]
        exact Finset.subset_inter xrp xrq
        --exact ⟨xrp, xrq⟩
      rw [disjoint] at xsub
      exact xsub

    --#check Finset.card_union_of_disjoint disjoint0
    convert (@Finset.sum_disjUnion _ _  rangeP rangeQ (λ s => s.card) _ disjoint0)
    simp
    rw [d_union]



----使ってない補題等
--結果的にtotal degree cardと同じことを示している。使ってない。
--lemma total_degone_card {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground)(gcard: F.ground.card ≥ 2) :
--  total_size_of_hyperedges F = (F.ground.powerset.filter (λ s => F.sets s ∧ v ∉ s )).sum Finset.card + F.ground.card
lemma filter_sum_one {α : Type} [DecidableEq α] [Fintype α] (F: IdealFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F.toSetFamily v = 1) (hasGround: F.sets F.ground)(gcard: F.ground.card ≥ 2):
    (Finset.filter (λ (s : Finset α) => F.sets s) F.ground.powerset).sum Finset.card = (Finset.filter (λ (s : Finset α) => (F.sets s ∧ v ∉ s)) F.ground.powerset).sum Finset.card + F.ground.card := by

  have degv: ¬ F.sets {v}:= by
        exact (degree_one_singleton F v hv gcard).mp deg1

  have eq: ∀ (s:Finset α), ((F.sets s ∧ v ∉ s) ∨ s = F.ground) ↔ F.sets s := by
    intro s
    apply Iff.intro
    swap
    · intro fsf
      by_cases h: v ∈ s
      · right
        apply Finset.ext
        intro x
        constructor
        intro a
        rw [←(degree_one_ground F v hv gcard deg1 s fsf h)]
        exact a
        intro a
        simp_all only [ge_iff_le]
        rw [(degree_one_ground F v hv gcard deg1 s fsf h)]
        exact a
      · left
        simp_all only [ge_iff_le, not_false_eq_true, and_self]
    · intro a
      simp_all only [ge_iff_le]
      cases a with
      | inl h => simp_all only
      | inr h_1 =>
        subst h_1
        simp_all only

  have disj: ∀ (s:Finset α), s ∈ F.ground.powerset → ¬((F.sets s ∧ v ∉ s) ∧ s = F.ground) := by
    intro s sh
    intro h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨left, right⟩ := h2
    exact h1.2 hv

  have ground_lem: F.ground.card = (Finset.filter (fun s => s = F.ground) F.ground.powerset).sum Finset.card := by
    rw [Finset.filter_eq']
    simp

  rw [ground_lem]

  have eqn0: (Finset.filter (fun s => F.sets s) F.ground.powerset) = (Finset.filter (fun s => (F.sets s ∧ v ∉ s) ∨ s = F.ground) F.ground.powerset) := by
    apply Finset.filter_congr
    intro s
    rw [Finset.mem_powerset]
    intro _
    rw [eq s]

  rw [eqn0]

  exact filter_sum (λ s => (F.sets s ∧ v ∉ s)) (λ s => s = F.ground) (F.ground.powerset) disj


--使ってないよう。
lemma degree_one_hyperedges_partition {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx: x ∈ F.ground) (h_not_hyperedge : ¬ F.sets {x}):
   ∀ (s:Finset α), (F.sets s) → ((s ≠ F.ground) ↔ x ∉ s) := by
  intro s hs
  apply Iff.intro
  · intro h
    by_contra h2
    have h3 := hyperedges_not_through_v F.toSetFamily x hx (degree_one_if_not_hyperedge F hx h_not_hyperedge) F.univ_mem s hs h
    contradiction
  · intro h
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    subst a
    simp_all only

--使ってないよう。
lemma degree_one_hyperedges_partition2 {α : Type} [DecidableEq α] [Fintype α]
  (F : IdealFamily α) (x : α) (hx: x ∈ F.ground):
   ∀ (s:Finset α),  s ∈ F.ground.powerset → ¬ ((x ∉ s ∧ F.sets s) ∧ (s = F.ground)):= by
  intro s
  intro sf
  by_contra h
  obtain ⟨h1, h2⟩ := h
  subst h2
  simp_all only

--使われてないよう。deg1を持つ集合族のhyperedge数は、vを含まないhyperedge数に1を足したもの。他の定理を使って、もっと簡単に証明できる可能性あり。
lemma erase_ground_card {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground)(gcard: F.ground.card ≥ 2) :
  number_of_hyperedges F = (F.ground.powerset.filter (λ s => F.sets s ∧ v ∉ s )).card + 1 := by
  --have h1 := trace_hyperedge_equiv F v hv deg1 hasGround gcard
  have disjoint_sets : Disjoint (Finset.filter (λ s => F.sets s ∧ s ≠ F.ground) (F.ground.powerset)) ({F.ground}) := by
    simp_all only [ne_eq, Set.union_singleton, Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_powerset,
      subset_refl, not_true_eq_false, and_false, not_false_eq_true]
  have h2 := Finset.card_union_of_disjoint disjoint_sets
  have whole:(Finset.filter (fun s => F.sets s ∧ s ≠ F.ground) F.ground.powerset ∪ {F.ground}) = Finset.filter (fun s => F.sets s) F.ground.powerset := by
    simp_all only [ne_eq, Set.union_singleton, Finset.disjoint_singleton_right, Finset.mem_filter,
      Finset.mem_powerset, subset_refl, not_true_eq_false, and_false, not_false_eq_true,
      Finset.card_union_of_disjoint, Finset.card_singleton]
    ext1 a
    simp_all only [Finset.mem_union, Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    apply Iff.intro
    · intro a_1
      cases a_1 with
      | inl h => simp_all only [and_self]
      | inr h_1 =>
        subst h_1
        simp_all only [subset_refl, and_self]
    · intro a_1
      simp_all only [true_and]
      tauto
  rw [whole] at h2
  rw [number_of_hyperedges]
  rw [h2]
  simp_all only [ge_iff_le, ne_eq, Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_powerset, subset_refl,
    not_true_eq_false, and_false, not_false_eq_true, Finset.card_singleton, add_left_inj]
  have h3 := hyperedges_not_through_v F v hv deg1 hasGround
  simp_all only [Finset.card_singleton, ne_eq]
  congr
  ext x : 2
  simp_all only [and_congr_right_iff]
  intro a
  apply Iff.intro
  · intro a_1
    simp_all only [not_false_eq_true]
  · intro a_1
    apply Aesop.BuiltinRules.not_intro
    intro a_2
    subst a_2
    simp_all only

-- 補助的な補題の定義 Fintype.card_eq_sum_onesと同じ。
--lemma card_eq_sum_ones {α : Type} [DecidableEq α][Fintype α]  (s : Finset α) :
--  Finset.card s = s.sum (λ a => 1) := by
--  simp_all only [Finset.sum_const, smul_eq_mul, mul_one]

end Ideal
