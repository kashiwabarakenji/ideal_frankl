import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import rooted.CommonDefinition
import rooted.RootedCircuits
import LeanCopilot

variable {α : Type} [DecidableEq α] [Fintype α]

open Finset
open Classical

lemma ground_nonempty_after_minor {α : Type} [DecidableEq α] (ground : Finset α) (x : α) (hx: x ∈ ground) (ground_ge_two: ground.card ≥ 2) : (ground.erase x).Nonempty :=
  by
    rw [Finset.erase_eq]
    apply Finset.nonempty_of_ne_empty
    by_contra h_empty
    by_cases hA : ground = ∅
    rw [hA] at ground_ge_two
    contradiction
    -- ground.card = 1のケース
    have g_eq_x: ground = {x} := by
      ext y
      constructor
      intro _
      have hy' : y ∈ ground \ {x} := by
          rw [h_empty]
          simp_all only [sdiff_eq_empty_iff_subset, subset_singleton_iff, false_or,card_singleton, Nat.not_ofNat_le_one]--
      rw [h_empty] at hy'
      contradiction
      -- y ∈ {x}のときに、groundに属することを示す
      intro hy
      have x_eq_y : x = y := by
        rw [mem_singleton] at hy
        rw [hy]
      rw [x_eq_y] at hx
      exact hx
    rw [g_eq_x] at ground_ge_two
    rw [Finset.card_singleton] at ground_ge_two
    contradiction

--traceコマンドと一緒にならないようにSetFamilyをつけた。
def SetFamily.trace {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2): SetFamily α :=
 /- haveI : DecidablePred (λ s => (x ∉ s) ∧ (F.sets s ∨ F.sets (s ∪ {x}))) :=
    λ s =>
      if h : x ∉ s then
        if hs : F.sets s then
          isTrue ⟨h, Or.inl hs⟩
        else if hs : F.sets (s ∪ {x}) then
          isTrue ⟨h, Or.inr hs⟩
        else
          isFalse (by simp_all)
      else
        isFalse (by simp_all)
-/
  { ground := F.ground.erase x,
    sets := λ s => (x ∉ s) ∧ (F.sets s ∨ F.sets (s ∪ {x})),
    nonempty_ground := ground_nonempty_after_minor F.ground x hx ground_ge_two,
    inc_ground := λ s hs =>
      by
        simp_all only [decide_eq_false_iff_not]
        obtain ⟨left, right⟩ := hs
        rw [Finset.subset_erase]
        constructor
        cases right with
        | inl hh =>
          exact F.inc_ground s hh
        | inr hh =>
          have hhh: s ∪ {x} ⊆ F.ground := F.inc_ground (s ∪ {x}) hh
          rename_i _ _ _ _ inst_3
          simp_all only [ge_iff_le]
          intro y hy
          exact hhh (mem_union_left _ hy)

        simp_all only [ge_iff_le, not_false_eq_true]
  }

  --closure systemのtraceがclosure systemであることを示す。DecidablePred F.setsを入れるとエラー。
instance trace_closure_system (F : ClosureSystem α) (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)  : ClosureSystem α :=
{
  ground := F.ground.erase x,
  sets := λ s => (x ∉ s) ∧ (F.sets s ∨ F.sets (s ∪ {x})),
  inc_ground :=
    by
      intro s hs
      rw [Finset.subset_erase]
      obtain ⟨left, right⟩ := hs
      constructor
      cases right with
      | inl hh =>
        exact F.inc_ground s hh
      | inr hh =>
        have hhh: s ∪ {x} ⊆ F.ground := F.inc_ground (s ∪ {x}) hh
        intro y hy
        exact hhh (mem_union_left _ hy)
      simp_all only [ge_iff_le, not_false_eq_true]
  nonempty_ground := ground_nonempty_after_minor F.ground x hx ground_ge_two,
  intersection_closed :=
    by
      intro s t hs ht
      constructor
      ·
        simp_all only [ge_iff_le, mem_inter, and_self, not_false_eq_true]
      · cases hs.2
        case inl hs1 =>
          cases ht.2
          case inl ht1 =>
            left
            exact F.intersection_closed s t hs1 ht1
          case inr ht1 =>
            left
            have : s ∩ (t ∪ {x}) = s ∩ t := by
              ext a : 1
              simp_all only [mem_inter, mem_union, mem_singleton]
              apply Iff.intro
              · intro a_1
                simp_all only [ge_iff_le, true_or, and_true, or_true, true_and]
                obtain ⟨left, right⟩ := a_1
                cases right with
                | inl h => simp_all only
                | inr h_1 =>
                  subst h_1
                  simp_all only
              · intro a_1
                simp_all only [and_true]
                tauto
            rw [←this]
            apply F.intersection_closed s (t ∪ {x}) hs1 ht1
        case inr hs1 =>
          cases ht.2
          case inl ht1 =>
            left
            have : (s ∪ {x}) ∩ t = s ∩ t := by
              ext a : 1
              simp_all only [mem_inter, mem_union, mem_singleton]
              apply Iff.intro
              · intro a_1
                simp_all only [ge_iff_le, true_or, and_true, or_true, true_and]
                obtain ⟨left, right⟩ := a_1
                cases left with
                | inl h => simp_all only
                | inr h_1 =>
                  subst h_1
                  simp_all only
              · intro a_1
                simp_all only [and_true]
                tauto
            rw [←this]
            exact F.intersection_closed (s ∪ {x}) t hs1 ht1
          case inr ht1 =>
            right
            have : (s ∪ {x}) ∩ (t ∪ {x}) = (s ∩ t) ∪ {x} := by
              ext a : 1
              simp_all only [mem_inter, mem_union, mem_singleton]
              apply Iff.intro
              · intro a_1
                simp_all only [ge_iff_le, true_or, and_true, or_true, true_and]
                obtain ⟨left, right⟩ := a_1
                cases left with
                | inl h =>
                  cases right with
                  | inl h_1 => simp_all only [and_self, true_or]
                  | inr h_2 =>
                    subst h_2
                    simp_all only
                | inr h_1 =>
                  cases right with
                  | inl h =>
                    subst h_1
                    simp_all only
                  | inr h_2 =>
                    subst h_1
                    simp_all only [and_self, or_true]
              · intro a_1
                simp_all only [ge_iff_le, or_true, and_true]
                cases a_1 with
                | inl h => simp_all only [true_or, and_self]
                | inr h_1 =>
                  subst h_1
                  simp_all only [or_true, and_self]
            rw [←this]
            exact F.intersection_closed (s ∪ {x}) (t ∪ {x}) hs1 ht1,
  has_ground :=
    by
      let thisF := SetFamily.trace (F.toSetFamily) x hx ground_ge_two
      have : thisF.sets (F.ground.erase x) := by
        constructor
        intro h
        simp at h
        right
        have : F.ground.erase x ∪ {x} = F.ground := by
          ext a : 1
          simp_all only [mem_union, mem_erase, ne_eq, mem_singleton]
          apply Iff.intro
          · intro a_1
            cases a_1 with
            | inl h => simp_all only
            | inr h_1 =>
              subst h_1
              simp_all only
          · intro a_1
            simp_all only [and_true]
            tauto
        convert F.has_ground
      simp
      dsimp [thisF] at this
      dsimp [SetFamily.trace] at this
      simp_all only [mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true, true_and]
}
 /-
  {
    ground := F.ground.erase x,

    sets := fun s => (SetFamily.trace (F.toSetFamily) x hx ground_ge_two).sets s

    has_ground :=
    by
      let thisF := SetFamily.trace (F.toSetFamily) x hx ground_ge_two
      have : thisF.sets (F.ground.erase x) := by
        constructor
        intro h
        simp at h
        right
        have : F.ground.erase x ∪ {x} = F.ground := by
          ext a : 1
          simp_all only [mem_union, mem_erase, ne_eq, mem_singleton]
          apply Iff.intro
          · intro a_1
            cases a_1 with
            | inl h => simp_all only
            | inr h_1 =>
              subst h_1
              simp_all only
          · intro a_1
            simp_all only [and_true]
            tauto
        convert F.has_ground
      simp
      exact this

    intersection_closed := by
      intro s t hs ht
      simp_all only
      dsimp [SetFamily.trace]
      dsimp [SetFamily.trace] at hs
      dsimp [SetFamily.trace] at ht
      constructor
      ·
        simp_all only [ge_iff_le, mem_inter, and_self, not_false_eq_true]

      · cases hs.2
        case inl hs1 =>
          cases ht.2
          case inl ht1 =>
            left
            exact F.intersection_closed s t hs1 ht1
          case inr ht1 =>
            left
            have : s ∩ (t ∪ {x}) = s ∩ t := by
              ext a : 1
              simp_all only [mem_inter, mem_union, mem_singleton]
              apply Iff.intro
              · intro a_1
                simp_all only [ge_iff_le, true_or, and_true, or_true, true_and]
                obtain ⟨left, right⟩ := a_1
                cases right with
                | inl h => simp_all only
                | inr h_1 =>
                  subst h_1
                  simp_all only
              · intro a_1
                simp_all only [and_true]
                tauto
            rw [←this]
            apply F.intersection_closed s (t ∪ {x}) hs1 ht1

        case inr hs1 =>
          cases ht.2
          case inl ht1 =>
            left
            have : (s ∪ {x}) ∩ t = s ∩ t := by
              ext a : 1
              simp_all only [mem_inter, mem_union, mem_singleton]
              apply Iff.intro
              · intro a_1
                simp_all only [ge_iff_le, true_or, and_true, or_true, true_and]
                obtain ⟨left, right⟩ := a_1
                cases left with
                | inl h => simp_all only
                | inr h_1 =>
                  subst h_1
                  simp_all only
              · intro a_1
                simp_all only [and_true]
                tauto
            rw [←this]
            exact F.intersection_closed (s ∪ {x}) t hs1 ht1
          case inr ht1 =>
            right
            have : (s ∪ {x}) ∩ (t ∪ {x}) =(s ∩ t) ∪ {x} := by
              ext a : 1
              simp_all only [mem_inter, mem_union, mem_singleton]
              apply Iff.intro
              · intro a_1
                simp_all only [ge_iff_le, true_or, and_true, or_true, true_and]
                obtain ⟨left, right⟩ := a_1
                cases left with
                | inl h =>
                  cases right with
                  | inl h_1 => simp_all only [and_self, true_or]
                  | inr h_2 =>
                    subst h_2
                    simp_all only
                | inr h_1 =>
                  cases right with
                  | inl h =>
                    subst h_1
                    simp_all only
                  | inr h_2 =>
                    subst h_1
                    simp_all only [and_self, or_true]
              · intro a_1
                simp_all only [ge_iff_le, or_true, and_true]
                cases a_1 with
                | inl h => simp_all only [true_or, and_self]
                | inr h_1 =>
                  subst h_1
                  simp_all only [or_true, and_self]
            rw [←this]
            exact F.intersection_closed (s ∪ {x}) (t ∪ {x}) hs1 ht1

    inc_ground := by
      intro s hs
      rw [subset_erase]
      dsimp [SetFamily.trace] at hs
      constructor
      ·
        cases hs.2
        case inl hs1 =>
          exact F.inc_ground s hs1
        case inr hs1 =>
          have hhh: s ∪ {x} ⊆ F.ground := F.inc_ground (s ∪ {x}) hs1
          simp_all only [ge_iff_le, or_true, and_true]
          intro y hy
          exact hhh (mem_union_left _ hy)
      · simp_all only [ge_iff_le, not_false_eq_true]

    nonempty_ground := ground_nonempty_after_minor F.ground x hx ground_ge_two
  }
-/
theorem trace_closure_system_rootedsets (F : ClosureSystem α)[DecidablePred F.sets] (x : α) (hx: x ∈ F.ground) (ground_ge_two: F.ground.card ≥ 2)[∀ s, Decidable (F.sets s)]:
  let RS := rootedSetsFromSetFamily F.toSetFamily
  --let _ : DecidablePred (SetFamily.trace (F.toSetFamily) x hx ground_ge_two).sets := by infer_instance
  let RSt := rootedSetsFromSetFamily (SetFamily.trace (F.toSetFamily) x hx ground_ge_two)
    ∀ p :ValidPair α, p ∈ RSt.rootedsets ↔ (p.root ≠ x ∧ x ∉ p.stem ∧ p ∈ RS.rootedsets) :=
  by
    let RSt := rootedSetsFromSetFamily (SetFamily.trace (F.toSetFamily) x hx ground_ge_two)
    simp
    intro p
    apply Iff.intro
    · intro h
      let p_inc := RSt.inc_ground p h
      dsimp [rootedSetsFromSetFamily] at h
      dsimp [rootedSetsSF] at h
      simp at h
      obtain ⟨h_left, h_right⟩ := h
      obtain ⟨h_left_1, h_right⟩ := h_right
      obtain ⟨h_left_2, h_right⟩ := h_right
      have rstground : RSt.ground = F.ground.erase x := by
        subst h_right
        simp_all only [RSt]
        obtain ⟨left, right⟩ := p_inc
        simp_all only [mem_image, mem_attach, ValidPair.mk.injEq, true_and, Subtype.exists, exists_and_left,
          exists_prop, Prod.exists, exists_eq_right, exists_eq_left, RSt]
        rfl
      constructor
      · let pinc2 := p_inc.2
        have :x ∉ RSt.ground := by
          dsimp [RSt]
          dsimp [SetFamily.trace]
          dsimp [rootedSetsFromSetFamily]
          subst h_right
          simp_all only [mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]
        subst h_right
        simp_all only [ne_eq, RSt]
        obtain ⟨left, right⟩ := p_inc
        simp_all only [mem_image, mem_attach, ValidPair.mk.injEq, true_and, Subtype.exists, exists_and_left,
          exists_prop, Prod.exists, exists_eq_right, exists_eq_left]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]
        simp [pinc2] at pinc2
        simp_all only [mem_erase, ne_eq, not_true_eq_false, and_true, RSt]
      · constructor
        · dsimp [allCompatiblePairs]
          let pinc1 := p_inc.1
          have: p.stem ⊆ RSt.ground := by
            subst h_right
            simp_all only [RSt]
            obtain ⟨left, right⟩ := p_inc
            simp_all only [mem_image, mem_attach, ValidPair.mk.injEq, true_and, Subtype.exists, exists_and_left,
              exists_prop, Prod.exists, exists_eq_right, exists_eq_left]
            exact left
          subst h_right
          simp_all only [ne_eq, RSt]
          obtain ⟨left, right⟩ := p_inc
          simp_all only [mem_image, mem_attach, ValidPair.mk.injEq, true_and, Subtype.exists, exists_and_left,
            exists_prop, Prod.exists, exists_eq_right, exists_eq_left]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp [a] at pinc1
          specialize pinc1 a
          simp_all only [mem_erase, ne_eq, not_true_eq_false, and_true, RSt]
        · show p ∈ (rootedSetsFromSetFamily F.toSetFamily).rootedsets
          dsimp [isCompatible]
          dsimp [rootedSetsFromSetFamily]
          dsimp [rootedSetsSF]
          simp
          subst h_right
          simp_all only [ValidPair.mk.injEq, exists_and_left, exists_prop, exists_eq_right, exists_eq_left, RSt]
          obtain ⟨left, right⟩ := p_inc
          simp_all only [mem_image, mem_attach, ValidPair.mk.injEq, true_and, Subtype.exists, exists_and_left,
            exists_prop, Prod.exists, exists_eq_right, exists_eq_left, mem_erase, ne_eq, RSt]
          obtain ⟨left_1, right⟩ := right
          dsimp [allCompatiblePairs]
          dsimp [isCompatible]
          dsimp [allPairs]
          rw [Finset.product]
          simp
          apply And.intro
          · apply Finset.mem_product.mpr
            constructor
            simp_all only [implies_true, and_self, true_and, Finset.mem_singleton, Finset.mem_powerset,
              Finset.singleton_subset_iff]
            rw [Finset.subset_iff] at left
            simp_all only [mem_erase, ne_eq]
            intro y hy
            simp_all only

            simp
            exact right

          · apply And.intro
            · show h_left_1 ∉ h_left
              dsimp [allCompatiblePairs] at h_left_2  --h_left_2の分解は上でやってもよい。
              dsimp [allPairs] at h_left_2
              dsimp [ Finset.product] at h_left_2
              have ⟨h_mem1, h_mem2⟩ := Finset.mem_filter.mp h_left_2
              dsimp [isCompatible] at h_mem2
              simp_all only [mem_filter, true_and, mem_mk, not_false_eq_true]

            · intro t a a_1
              show h_left_1 ∈ t --tがxを含むかどうかで場合分けの必要があるかも。
              dsimp [allCompatiblePairs] at h_left_2
              dsimp [allPairs] at h_left_2
              rw [Finset.product] at h_left_2
              have ⟨h_mem1, h_mem2⟩ := Finset.mem_filter.mp h_left_2
              dsimp [isCompatible] at h_mem2
              by_cases ht: x ∈ t
              case pos =>
                have :h_left_1 ∈ t.erase x := by
                  apply h_mem2.2 (t.erase x)
                  · simp_all only [mem_filter, true_and, mem_mk]
                    constructor
                    · simp_all only [mem_erase, ne_eq, not_true_eq_false, and_true, not_false_eq_true]
                    · right
                      have : t.erase x ∪ {x} = t := by
                        ext a : 1
                        simp_all only [mem_union, mem_erase, ne_eq, mem_singleton]
                        apply Iff.intro
                        · intro a_1
                          cases a_1 with
                          | inl h => simp_all only
                          | inr h_1 =>
                            subst h_1
                            simp_all only
                        · intro a_1
                          simp_all only [and_true]
                          tauto
                      rw [←this]
                      simp_all only
                  · have : x ∉ h_left := by
                      simp at  h_mem1
                      dsimp [SetFamily.trace] at h_mem1
                      have :h_left ∈ (F.ground.erase x).powerset.val ∧ h_left_1 ∈ F.ground.val.erase x :=
                      by
                        apply (@Finset.mem_product _ _ (F.ground.erase x).powerset (F.ground.erase x)).mp h_mem1
                      simp at this
                      let t1 := this.1
                      rw [Finset.subset_erase] at t1
                      simp_all only [mem_filter, mem_mk, not_false_eq_true]
                    simp_all only [mem_filter, true_and, mem_mk]
                    obtain ⟨left_2, right_1⟩ := h_mem2
                    intro y hy
                    simp_all only [mem_erase, ne_eq]
                    apply And.intro
                    · apply Aesop.BuiltinRules.not_intro
                      intro a_2
                      subst a_2
                      simp_all only
                    · exact a_1 hy
                simp_all only [mem_filter, true_and, mem_mk, mem_erase, ne_eq, not_false_eq_true]

              case neg =>
                apply h_mem2.2 t --これが正しいのか。tがxを含むかどうかで場合分け？
                · simp_all only [mem_filter, true_and, mem_mk]
                  obtain ⟨left_2, right_1⟩ := h_mem2
                  dsimp [SetFamily.trace]
                  constructor
                  · exact ht
                  · simp_all only [true_or]
                ·exact a_1
    · intro h
      have rstground : RSt.ground = F.ground.erase x := by
        simp_all only [RSt]
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        rfl

      have traceground: (F.trace x hx ground_ge_two).ground = F.ground.erase x :=
      by
        simp_all only [RSt]
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        exact rstground
      have pinc := (rootedSetsFromSetFamily F.toSetFamily).inc_ground p h.2.2
      dsimp [rootedSetsFromSetFamily]
      dsimp [rootedSetsSF]
      --dsimp [allCompatiblePairs]
      --dsimp [allPairs]
      simp
      use p.stem
      use p.root
      have :(p.stem, p.root) ∈ allCompatiblePairs (F.trace x hx ground_ge_two) := by
        dsimp [allCompatiblePairs]
        dsimp [allPairs]
        rw [Finset.product]
        simp
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        apply And.intro
        · apply Finset.mem_product.mpr
          constructor
          · simp_all only [implies_true, and_self, true_and, Finset.mem_singleton, Finset.mem_powerset,
              Finset.singleton_subset_iff]
            let hxyground := right
            dsimp [RSt] at rstground
            rw [Finset.subset_erase]
            constructor
            · obtain ⟨left_2, right_1⟩ := pinc
              exact left_2
            · simp_all only [not_false_eq_true]
          · simp
            dsimp [SetFamily.trace]
            rw [Finset.erase_eq]
            simp
            let rsi := (rootedSetsFromSetFamily F.toSetFamily).inc_ground p right
            constructor
            exact rsi.2
            exact left

        · dsimp [isCompatible]
          constructor
          · exact p.root_not_in_stem
          · intro t a a_1
            dsimp [rootedSetsFromSetFamily] at right
            dsimp [rootedSetsSF] at right
            dsimp [allCompatiblePairs] at right
            dsimp [isCompatible] at right
            simp at right
            obtain ⟨left, right_1⟩ := right
            obtain ⟨left_1, right⟩ := right_1
            obtain ⟨left_2, right_1⟩ := right
            let left_22 := left_2.2.2
            dsimp [SetFamily.trace] at a
            cases a.2
            case inl => --(F.sets t ∨ F.sets (t ∪ {x}))
              subst right_1
              simp_all only [true_or, RSt]
            case inr a2r =>
              let left_22x := left_22 (t ∪ {x}) a2r
              have :p.root = left_1 := by
                subst right_1
                simp_all only [or_true, and_true, RSt]
              subst left_1
              have :p.stem = left := by
                simp_all only [or_true, and_true, RSt]
                obtain ⟨left_2, right⟩ := left_2
                obtain ⟨left_4, right_2⟩ := pinc
                obtain ⟨left_5, right⟩ := right
                rw [← right_1]
              have :p.root ∈ t ∪ {x} := by
                apply left_22x
                subst this
                simp_all only [or_true, and_true, RSt]
                obtain ⟨left, right⟩ := left_2
                obtain ⟨left_2, right_1⟩ := pinc
                obtain ⟨left_4, right⟩ := right
                intro y hy
                simp_all only [mem_union, mem_singleton]
                apply Or.inl
                apply a_1
                simp_all only
              rename_i this_1
              subst this_1
              simp_all only [or_true, and_true, mem_union, mem_singleton, or_false, RSt]
      simp_all only [exists_const]
