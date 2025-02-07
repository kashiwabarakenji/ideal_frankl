--importする必要がない、RootedSetsに関する定理
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Prod
import rooted.CommonDefinition
import rooted.ClosureOperator
import rooted.RootedSets
import rooted.ClosureMinors
import Mathlib.Tactic
import LeanCopilot

-- 有限集合の型
variable {α : Type} [Fintype α] [DecidableEq α]

open Classical

def SetFamily.is_bridge (SF : SetFamily α) (x : α) : Prop := ∀ s, SF.sets s → x ∈ s

--xはsubtype。
theorem rooted_sets_bridge (SF : ClosureSystem α)  [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (x:SF.ground):
let RS := rootedSetsFromSetFamily SF.toSetFamily
SF.is_bridge x ↔ ∃ (r : ValidPair α), r ∈ RS.rootedsets ∧ r.root = x ∧ r.stem = ∅ :=
by
  intro RS
  constructor
  · intro h
    have : x.val ∉ (∅:Finset α) := by simp
    let v := ValidPair.mk ∅ x.val this
    use v
    constructor
    dsimp [RS]
    dsimp [rootedSetsFromSetFamily]
    dsimp[rootedSetsSF]
    dsimp [allCompatiblePairs]
    dsimp [isCompatible]
    simp
    use v.stem
    use v.root
    constructor
    rfl
    constructor
    dsimp [allPairs]
    rw [Finset.product]
    simp
    apply Finset.mem_product.mpr
    constructor
    simp
    simp
    constructor
    exact v.root_not_in_stem
    intro t a a_1
    simp_all only [Finset.empty_subset]
    apply h
    simp_all only
    simp_all only [and_self]

  · intro h
    simp_all only [RS]
    obtain ⟨val, property⟩ := x
    obtain ⟨w, h⟩ := h
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    subst left_1
    dsimp [SetFamily.is_bridge]
    intro s hs
    dsimp [rootedSetsFromSetFamily] at left
    dsimp [rootedSetsSF] at left
    dsimp [allCompatiblePairs] at left
    dsimp [isCompatible] at left
    simp at left
    obtain ⟨w_1, h⟩ := left
    obtain ⟨w_2, h⟩ := h
    obtain ⟨w_3, h⟩ := h
    subst h
    subst right
    simp_all only [Finset.empty_subset]

    --そのほかbridgeに関して、traceしたらどうなるかとか、bridgeのない集合族だけを考えればフランクルの予想には十分だとかいろいろ考えられる。

--bridgeをtraceしてもhyperedgeの数は変わらないという定理。
theorem trace_bridge_keep_hyperedge (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (geq2: SF.ground.card ≥ 2) (x:SF.ground):
  SF.is_bridge x →
   SF.number_of_hyperedges = (SF.trace x.val x.property geq2).number_of_hyperedges :=
by
  intro h_br
  let SF':= SF.trace x.val x.property geq2
  let S := SF.ground.powerset.filter (fun s => SF.sets s)
  let S' := SF'.ground.powerset.filter (fun s => SF'.sets s)
  have sground: SF'.ground = SF.ground.erase x.val := by
    simp [SF']
    obtain ⟨val, property⟩ := x
    simp_all only [Subtype.mk.injEq]
    rfl

  have hi: ∀ (s:S),  (s.val).erase x.val ∈ S' := by
    dsimp [S', S]
    intro s
    have h := s.property
    rw [Finset.mem_filter]
    constructor
    · simp_all only [ne_eq, Finset.coe_mem, Finset.mem_powerset, S]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_s, s_prop⟩ := s
      simp_all only [Subtype.mk.injEq]
      simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
      obtain ⟨left, right⟩ := s_prop
      simp_all only [SF']
      intro x hx
      simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
      obtain ⟨left_1, right⟩ := hx
      exact left right
    · constructor
      · simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
      · right
        simp_all only [ne_eq, Finset.coe_mem, SF']
        obtain ⟨val, property⟩ := x
        obtain ⟨val_2, property_2⟩ := s
        simp_all only [Subtype.mk.injEq]
        simp_all only [Finset.mem_filter, Finset.mem_powerset, and_true]
        obtain ⟨left, right⟩ := property_2
        convert right
        ext a : 1
        simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, Finset.mem_singleton]
        apply Iff.intro
        · intro a_1
          cases a_1 with
          | inl h => simp_all only
          | inr h_1 =>
            subst h_1
            apply h_br
            simp_all only
        · intro a_1
          simp_all only [and_true]
          tauto

  let i:S → S' := fun s => ⟨s.val.erase x.val, by
    simp_all only [ne_eq, Finset.mem_filter, Finset.mem_powerset, Subtype.forall, forall_const, and_imp, SF', S, S']
    obtain ⟨val, property⟩ := x
    obtain ⟨val_2, property_2⟩ := s
    simp_all only [Subtype.mk.injEq]
    simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, S]
  ⟩

  let ii: (s : Finset α) → s ∈ S → Finset α := fun (s:Finset α) (hs:s ∈ S) => s.erase x.val

  have hi2: ∀ (s : Finset α) (hs : s ∈ S), ii s hs ∈ S' :=
  by
    intro s hs
    exact hi ⟨s, hs⟩

  have inj: ∀ (a₁ : Finset α) (ha₁ : a₁ ∈ S) (a₂ : Finset α) (ha₂ : a₂ ∈ S), ii a₁ ha₁ = ii a₂ ha₂ → a₁ = a₂ :=
  by
    intro a1 ha1 a2 ha2 h
    dsimp [ii] at h
    simp at h
    dsimp [SetFamily.is_bridge] at h_br
    ext y : 1
    constructor
    · intro hh
      simp at hh
      by_cases y = x.val
      case pos =>
        dsimp [S] at ha2
        have : y ∈ a2 := by
          rw [Finset.mem_filter] at ha2
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, S, S', SF', ii]
        exact this
      case neg =>
        have: y ∈ a1.erase x.val := by
          rw [@Finset.mem_erase]
          simp_all only [and_imp, ne_eq, not_false_eq_true, and_self, ii, S]
        have: y ∈ a2.erase x.val := by
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_erase, ne_eq, not_false_eq_true,
            true_and, and_self, S, S', SF', ii]
        simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_erase, ne_eq, not_false_eq_true,
          true_and, S, S', SF', ii]

    · intro hh
      by_cases y = x.val
      case pos =>
        dsimp [S] at ha1
        rw [Finset.mem_filter] at ha1
        have : y ∈ a1 := by
          rename_i h_1
          subst h_1
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, S, S', SF', ii]
        exact this
      case neg =>
        have: y ∈ a2.erase x.val := by
          rw [@Finset.mem_erase]
          simp_all only [and_imp, ne_eq, not_false_eq_true, and_self, ii, S]
        have: y ∈ a1.erase x.val := by
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_erase, ne_eq, not_false_eq_true,
            true_and, and_self, S, S', SF', ii]
        rw [Finset.mem_erase] at this
        exact this.2

  have surj: ∀ b ∈ S', ∃ a, ∃ (ha : a ∈ S), ii a ha = b :=
  by
    dsimp [S,S']
    intro b hb
    use insert x.val b
    dsimp [SetFamily.is_bridge] at h_br
    rw [Finset.mem_filter] at hb
    dsimp [SF'] at hb
    dsimp [SetFamily.trace] at hb
    obtain ⟨hb1,hb2,hb3⟩ := hb
    have :insert (x.val) b ∈ Finset.filter (fun s => SF.sets s) SF.ground.powerset :=
    by
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
        rw [@Finset.insert_subset_iff]
        constructor
        · simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, and_imp, subset_refl, Finset.coe_mem, S, S', SF',
            ii]
        ·
          cases hb3 with
          | inl h =>
            exfalso
            exact hb2 (h_br b h)
          | inr h =>
            rw [Finset.mem_powerset] at hb1
            rw [@Finset.subset_erase] at hb1
            exact hb1.1

      ·
        simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, and_imp, subset_refl,
          Finset.singleton_subset_iff, Finset.coe_mem, S, S', SF', ii]
        obtain ⟨val, property⟩ := x
        simp_all only [subset_refl, Finset.singleton_subset_iff]
        cases hb3 with
        | inl h => simp_all only [subset_refl, not_true_eq_false]
        | inr h_1 =>
          rw [Finset.union_comm] at h_1
          exact h_1

    simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, and_imp, subset_refl, Finset.singleton_subset_iff,
      Finset.coe_mem, Finset.erase_insert_eq_erase, not_false_eq_true, Finset.erase_eq_of_not_mem, exists_const, S,
      S', SF', ii]

  have card_eq: S.card = S'.card := by
    apply @Finset.card_bij _ _ S S' ii hi2 inj surj

  dsimp [SetFamily.number_of_hyperedges, SetFamily.trace]
  dsimp [S,S'] at card_eq
  simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, and_imp, subset_refl, exists_prop,
    Finset.singleton_subset_iff, Finset.coe_mem, Nat.cast_inj, S, S', SF', ii]
  obtain ⟨val, property⟩ := x
  simp_all only [subset_refl, Finset.singleton_subset_iff]
  rfl

--bridgeのtraceをしてもdegreeが変化しないこと。
theorem trace_bridge_keep_degree (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (geq2: SF.ground.card ≥ 2) (x:SF.ground):
  SF.is_bridge x →
  ∀ (y:SF.ground), x≠y →
   SF.degree y = (SF.trace x.val x.property geq2).degree y :=
by
  intro h_br
  intro y h_neq
  let SF':= SF.trace x.val x.property geq2
  let S := SF.ground.powerset.filter (fun s => SF.sets s ∧ y.val ∈ s)
  let S' := SF'.ground.powerset.filter (fun s => SF'.sets s∧ y.val ∈ s)
  have sground: SF'.ground = SF.ground.erase x.val := by
    simp [SF']
    obtain ⟨val, property⟩ := x
    simp_all only [Subtype.mk.injEq]
    rfl

  have hi: ∀ (s : Finset α), (s ∈ S)  → (s.erase x.val ∈ S') := by
    dsimp [S', S]
    intro s hs
    simp_all only [ne_eq, Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, and_true, SF']
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    obtain ⟨left, right⟩ := hs
    obtain ⟨left_1, right⟩ := right
    simp_all only [Subtype.mk.injEq]
    apply And.intro
    ·
      intro x hx
      simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
      obtain ⟨left_2, right_1⟩ := hx
      exact left right_1
    · apply And.intro
      · dsimp [SetFamily.trace]
        constructor
        ·
          simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
        · right
          have: s.erase val ∪ {val} = s := by
            ext a : 1
            simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, Finset.mem_singleton]
            apply Iff.intro
            · intro a_1
              cases a_1 with
              | inl h => simp_all only
              | inr h_1 =>
                subst h_1
                apply h_br
                simp_all only
            · intro a_1
              simp_all only [and_true]
              tauto
          simp_all only
      · apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [not_true_eq_false]

  let i:S → S' := fun s => ⟨s.val.erase x.val, by
    simp_all only [ne_eq, Finset.mem_filter, Finset.mem_powerset, and_imp, SF', S, S']
    obtain ⟨val_2, property_2⟩ := s
    simp_all only [Subtype.mk.injEq]
    simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, S]
  ⟩
  let ii: (s : Finset α) → s ∈ S → Finset α := fun (s:Finset α) (hs:s ∈ S) => s.erase x.val

  have hi2: ∀ (s : Finset α) (hs : s ∈ S), ii s hs ∈ S' :=
  by
    intro s hs
    exact hi s hs

  have inj: ∀ (a₁ : Finset α) (ha₁ : a₁ ∈ S) (a₂ : Finset α) (ha₂ : a₂ ∈ S), ii a₁ ha₁ = ii a₂ ha₂ → a₁ = a₂ :=
  by
    intro a1 ha1 a2 ha2 h
    dsimp [ii] at h
    simp at h
    dsimp [SetFamily.is_bridge] at h_br
    ext y : 1
    constructor
    · intro hh
      simp at hh
      by_cases y = x.val
      case pos =>
        dsimp [S] at ha2
        have : y ∈ a2 := by
          rw [Finset.mem_filter] at ha2
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, S, S', SF', ii]
        exact this
      case neg =>
        have: y ∈ a1.erase x.val := by
          rw [@Finset.mem_erase]
          simp_all only [and_imp, ne_eq, not_false_eq_true, and_self, ii, S]
        have: y ∈ a2.erase x.val := by
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_erase, ne_eq, not_false_eq_true,
            true_and, and_self, S, S', SF', ii]
        simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_erase, ne_eq, not_false_eq_true,
          true_and, S, S', SF', ii]

    · intro hh
      by_cases y = x.val
      case pos =>
        dsimp [S] at ha1
        rw [Finset.mem_filter] at ha1
        have : y ∈ a1 := by
          rename_i h_1
          subst h_1
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, S, S', SF', ii]
        exact this
      case neg =>
        have: y ∈ a2.erase x.val := by
          rw [@Finset.mem_erase]
          simp_all only [and_imp, ne_eq, not_false_eq_true, and_self, ii, S]
        have: y ∈ a1.erase x.val := by
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_erase, ne_eq, not_false_eq_true,
            true_and, and_self, S, S', SF', ii]
        exact Finset.mem_of_mem_erase this

  have surj: ∀ b ∈ S', ∃ a, ∃ (ha : a ∈ S), ii a ha = b :=
  by
    dsimp [S,S']
    intro b hb
    use insert x.val b
    dsimp [SetFamily.is_bridge] at h_br
    rw [Finset.mem_filter] at hb
    dsimp [SF'] at hb
    dsimp [SetFamily.trace] at hb
    obtain ⟨hb1,hb2,hb3⟩ := hb
    have :insert (x.val) b ∈ Finset.filter (fun s => SF.sets s) SF.ground.powerset :=
    by
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powerset]
        rw [@Finset.insert_subset_iff]
        constructor
        · simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, and_imp, subset_refl, Finset.coe_mem, S, S', SF',
            ii]
        ·
          simp_all only [ne_eq, Finset.mem_filter, Finset.mem_powerset, and_self, implies_true, and_imp, subset_refl,
            Finset.singleton_subset_iff, Finset.coe_mem, S, S', SF', ii]
          obtain ⟨val, property⟩ := x
          obtain ⟨val_1, property_1⟩ := y
          obtain ⟨left, right⟩ := hb2
          simp_all only [subset_refl, Subtype.mk.injEq, Finset.singleton_subset_iff]
          cases right with
          | inl h => simp_all only [subset_refl, not_true_eq_false]
          | inr h_1 =>
            intro x hx
            have hx' : x ∈ SF.ground.erase val := hb1 hx
            simp_all only [subset_refl, Finset.singleton_subset_iff, Finset.mem_erase, ne_eq]
      ·
        simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, and_imp, subset_refl,
          Finset.singleton_subset_iff, Finset.coe_mem, S, S', SF', ii]
        obtain ⟨val, property⟩ := x
        simp_all only [subset_refl, Finset.singleton_subset_iff]
        have : ¬ SF.sets b :=
        by
          simp_all only [subset_refl, implies_true, ne_eq, Finset.singleton_subset_iff]
          obtain ⟨val_1, property_1⟩ := y
          obtain ⟨left, right⟩ := hb2
          simp_all only [subset_refl, Subtype.mk.injEq, Finset.singleton_subset_iff]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [subset_refl, not_true_eq_false]
        have :SF.sets (b ∪ {val}):=
        by
          simp_all only [subset_refl, implies_true, ne_eq, Finset.singleton_subset_iff, false_or]
        have : b ∪ {val} = insert val b := by
          simp_all only [subset_refl, implies_true, ne_eq, Finset.singleton_subset_iff, or_true, and_true]
          obtain ⟨val_1, property_1⟩ := y
          simp_all only [subset_refl, Finset.singleton_subset_iff, Subtype.mk.injEq]
          ext a : 1
          simp_all only [subset_refl, Finset.singleton_subset_iff, Finset.mem_union, Finset.mem_singleton,
            Finset.mem_insert]
          apply Iff.intro
          · intro a_1
            cases a_1 with
            | inl h => simp_all only [subset_refl, Finset.singleton_subset_iff, or_true]
            | inr h_1 =>
              subst h_1
              simp_all only [subset_refl, Finset.singleton_subset_iff, or_false]
          · intro a_1
            cases a_1 with
            | inl h =>
              subst h
              simp_all only [subset_refl, Finset.singleton_subset_iff, or_true]
            | inr h_1 => simp_all only [subset_refl, Finset.singleton_subset_iff, true_or]
        simp_all only [subset_refl, implies_true, ne_eq, Finset.singleton_subset_iff, false_or]

    simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, and_imp, subset_refl, Finset.singleton_subset_iff,
      Finset.coe_mem, Nat.cast_inj, S, S', SF', ii]
    simp_all only [ne_eq, subset_refl, implies_true, Finset.singleton_subset_iff, Finset.coe_mem,
      Finset.erase_insert_eq_erase, not_false_eq_true, Finset.erase_eq_of_not_mem, Finset.mem_insert, or_true,
      and_self, exists_const]

  have card_eq: S.card = S'.card := by
    apply @Finset.card_bij _ _ S S' ii hi2 inj surj

  dsimp [SetFamily.degree, SetFamily.trace]
  simp
  dsimp [S,S'] at card_eq
  convert card_eq

  --bridgeは、rare vertexではない。
  lemma bridge_degree (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (x:SF.ground):
    SF.is_bridge x →
    SF.degree x = SF.number_of_hyperedges :=
  by
    intro h_br
    simp_all only [SetFamily.degree, SetFamily.number_of_hyperedges, SetFamily.trace]
    simp_all only [ge_iff_le, Int.ofNat_eq_coe, Nat.cast_inj]
    obtain ⟨val, property⟩ := x
    simp_all only
    congr
    ext x : 2
    simp_all only [and_iff_left_iff_imp]
    intro a
    exact h_br _ a

  --bridgeのvertexは、rare vertexではない。
  lemma bridge_notrare (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (x:SF.ground):
    SF.is_bridge x → ¬ SF.is_rare x :=
  by
    intro h_br
    intro h_rare
    have h_deg := bridge_degree SF  x h_br
    dsimp [SetFamily.is_rare] at h_rare
    simp_all
    rw [←h_deg] at h_rare
    ring_nf at h_rare
    have: SF.degree x > 0 :=
    by
      dsimp [SetFamily.degree]
      simp
      use SF.ground
      rw [Finset.mem_filter]
      constructor
      simp_all only [Finset.mem_powerset, subset_refl]
      constructor
      ·
        exact SF.has_ground
      ·
        exact Finset.coe_mem x
    simp_all only [gt_iff_lt, mul_le_iff_le_one_right, Nat.not_ofNat_le_one]

    --bridgeをtraceしても、rare vertexが存在するかは変わらない。
  lemma trace_bridge_rare (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (geq2: SF.ground.card ≥ 2) (x:SF.ground):
    SF.is_bridge x →
    ∀ (y:SF.ground), x≠y →
    (SF.is_rare y ↔ (SF.trace x.val x.property geq2).is_rare y) :=
  by
    intro h_br
    intro y
    intro h_neq
    --
    apply Iff.intro
    ·
      intro h_rare
      --trace_bridge_keep_degreeとtrace_bridge_keep_hyperedgeを使う。
      have h_deg := trace_bridge_keep_degree SF geq2 x h_br y h_neq
      have h_deg' := trace_bridge_keep_hyperedge SF geq2 x h_br
      dsimp [SetFamily.is_rare] at h_rare
      dsimp [SetFamily.is_rare]
      simp_all only [ne_eq, tsub_le_iff_right, zero_add]
    ·
      intro h_rare
      have h_deg := trace_bridge_keep_degree SF geq2 x h_br y h_neq
      have h_deg' := trace_bridge_keep_hyperedge SF geq2 x h_br
      dsimp [SetFamily.is_rare] at h_rare
      dsimp [SetFamily.is_rare]
      simp_all only [ne_eq, tsub_le_iff_right, zero_add]

def isBridgeFree (SF : ClosureSystem α) [DecidablePred SF.sets] : Prop :=
  ∀ (v : α), v ∈ SF.ground → ¬ SF.is_bridge v

noncomputable instance decidableIsBridgeFree (SF : ClosureSystem α) [DecidablePred SF.sets] : Decidable (isBridgeFree SF) :=
  inferInstance

def P_has_bridge {α : Type} [DecidableEq α] [Fintype α] (n : Nat) : Prop :=
   (∀ (F : ClosureSystem α) [DecidablePred F.sets], F.ground.card = n → ∃ u, F.is_bridge u → ∃ (v : α), v ∈ F.ground ∧ F.is_rare v)

def P_has_empty {α : Type} [DecidableEq α] [Fintype α] (n : Nat) : Prop :=
   (∀ (F : ClosureSystem α) [DecidablePred F.sets], F.ground.card = n → F.has_empty → (∃ u, u ∉ F.ground) → ∃ (v : α), v ∈ F.ground ∧ F.is_rare v)



theorem bridge_free_theorem {α : Type} [Infinite α] [Fintype α] [DecidableEq α] :
  (∀ (n : Nat), @P_has_bridge α _ _ n) ↔ (∀ (n : Nat), @P_has_empty α _ _ n) :=
by
  apply Iff.intro
  · -- bridgeを持つ場合にrare vertexが存在したとすると、emptyを持つ場合にもrare vertexが存在することを示す。
    dsimp [P_has_bridge,P_has_empty]
    intro h --bridgeを持つ場合の仮定
    intro n
    intro F inst_1 a a_1
    intro eu
    obtain ⟨u, hu⟩ := eu
    --ここから新しい集合族を考えたい。
    --台集合は、F.groundにuを加えたもの。
    --F.setsとなるhyperedgeは、F.sets sを満たすsにuを加えたもの。s cup u
    --今のままだとF.sets sに対して、
    let F' := SetFamily.mk (insert u F.ground) (fun s => u ∈ s ∧ F.sets (s.erase u)) (by --inc_ground
      intro s
      simp
      intro su
      intro sfs
      intro x
      rw [Finset.mem_insert]
      intro hx
      by_cases hxu: x = u
      case pos =>
        left
        exact hxu
      case neg =>
        right
        have : x ∈ s.erase u :=
        by
          subst a
          simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self]
        have :s.erase u ⊆ F.ground :=
        by
          exact F.inc_ground (s.erase u) sfs
        subst a
        simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self]
        apply this
        simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self]
    ) (by --nonempty_ground
    subst a
    simp_all only [Finset.insert_nonempty]
    ) --ここまででF'の構築。

    have F'_closure : ClosureSystem α :=
    { ground := F'.ground
      sets := F'.sets
      inc_ground := F'.inc_ground
      nonempty_ground := F'.nonempty_ground
      intersection_closed :=
      by
        simp
        intro s t
        intro hs hss
        intro ht hst
        constructor
        subst a
        simp_all only [and_self]

        have : s.erase u ∩ t.erase u = (s ∩ t).erase u :=
        by
          subst a
          simp_all only [Finset.erase_inter, Finset.mem_inter, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
            and_false, not_false_eq_true, Finset.erase_eq_of_not_mem]
          ext a : 1
          simp_all only [Finset.mem_inter, Finset.mem_erase, ne_eq]
          apply Iff.intro
          · intro a_2
            simp_all only [not_false_eq_true, and_self]
          · intro a_2
            simp_all only [not_false_eq_true, and_self]
        rw [←this]
        exact F.intersection_closed (s.erase u) (t.erase u) hss hst

      has_ground :=
      by
        constructor
        simp
        convert F.has_ground
        simp
        exact hu
    }

    have F'ground: F'.ground.card = n + 1 :=
    by
      subst a
      simp_all only [not_false_eq_true, Finset.card_insert_of_not_mem]

    have :(insert u F.ground).card = n + 1 :=
    by
      subst a
      simp_all only [not_false_eq_true, Finset.card_insert_of_not_mem]

    --#check F'_closure.ground

    --have F'closureground : F'_closure.ground.card = F'.ground.card :=
    --by
    --  sorry

    have F'closureground: F'_closure.ground.card = n + 1 :=
    by
      sorry

    --#check h (n+1) F'_closure F'closureground

    sorry

  · -- 帰納法による方向: Bridge-Free でない場合に Bridge を除去して帰納仮定を適用
    intro h
    intro n
    dsimp [P_has_empty] at h
    dsimp [P_has_bridge]
    intro F inst_1 h_size
    by_cases h_bridge : F.has_empty
    apply @Nat.strong_induction_on (λ n => @P_has_bridge α _ _ n)
    intros n ih F dp fgc
    sorry
    sorry
    /-
    by_cases h_bridge : @P_has_empty α _ _ n F dp fgc
    case pos =>
      -- F が Bridge を持たない場合、PP_Bridge n を直接適用
      specialize h n F fgc h_bridge
      obtain ⟨v, hv_ground, hv_rare, _⟩ := h
      use v
    -/
    case neg =>
      -- F が Bridge を持つ場合、Bridge を削除して帰納仮定を適用
      dsimp [ClosureSystem.has_empty] at h_bridge
      sorry
      /-
      push_neg at h_bridge
      obtain ⟨v, hv_ground, hv_bridge⟩ := h_bridge
      have h_ground_card' : F.ground.card ≥ 1 := by
        subst fgc h_size
        simp_all only [and_true, ge_iff_le, Finset.one_le_card]
        use v
      by_cases gc: F.ground.card = 1
      case pos =>
        dsimp [SetFamily.is_rare]
        -- F が 1 つの頂点だけからなる場合、その頂点は rare vertex である
        -- 唯一の頂点を取り出す。vvとする。
        -- F.has_groundより、全体集合がhyperedgeである。空集合がhyperedgeであっても、なくてもvvは、rareとなる。
        -- なぜなら、vvが含まれるhyperedgeがあるとすると、vvを含むhyperedgeは、全体集合のみである。
        -- このとき、vvを含むhyperedgeは、全体集合のみである。全体集合は、hyperedgeである。よって、vvは、rare vertexである。
        dsimp [SetFamily.degree]
        dsimp [SetFamily.number_of_hyperedges]

        rw [Finset.card_eq_one] at gc
        obtain ⟨vv, h_vv⟩ := gc
        use vv
        constructor
        subst fgc h_size
        simp_all only [and_true, Finset.mem_singleton, Finset.card_singleton, ge_iff_le, le_refl, Nat.lt_one_iff,
          forall_eq]
        simp
        have pow: ({vv}:Finset α).powerset = {∅, {vv}} := by
          ext a : 1
          simp_all only [Finset.mem_powerset, Finset.mem_singleton, Finset.mem_insert, Finset.mem_singleton]
          apply Iff.intro
          · intro a_1
            subst h_size fgc hv_ground
            simp_all only [and_true, Finset.subset_singleton_iff, Finset.card_singleton, Nat.lt_one_iff, forall_eq,
              ge_iff_le, le_refl]
          · intro a_1
            cases a_1 with
            | inl h =>
              subst h_size fgc hv_ground h
              simp_all only [and_true, Finset.card_singleton, Nat.lt_one_iff, forall_eq, ge_iff_le, le_refl,
                Finset.subset_singleton_iff, true_or]
            | inr h_1 =>
              subst h_1
              subst h_size fgc hv_ground
              simp_all only [and_true, Finset.card_singleton, Nat.lt_one_iff, forall_eq, ge_iff_le, le_refl,
                subset_refl]
        simp_all only [Finset.mem_singleton, Finset.mem_powerset, Finset.empty_subset, and_self]
        rw [←pow]
        rw [@Finset.card_filter]
        rw [@Finset.card_filter]
        simp_all only [Finset.mem_singleton, Finset.mem_powerset, Finset.empty_subset, and_self]
        rw [Finset.sum_insert]
        rw [Finset.sum_singleton]

        by_cases fe: F.sets ∅
        case pos =>
          subst h_size fgc hv_ground
          simp_all only [and_true, Finset.card_singleton, Nat.lt_one_iff, forall_eq, ge_iff_le, le_refl,
            Finset.not_mem_empty, and_false, ↓reduceIte, Finset.mem_singleton, zero_add, Nat.cast_ite, Nat.cast_one,
            CharP.cast_eq_zero, mul_ite, mul_one, mul_zero, Finset.sum_boole, Nat.cast_id]
          split
          next h_1 =>
            simp_all only [Nat.ofNat_le_cast]
            rw [@Finset.card_filter]
            rw [Finset.sum_insert]
            rw [Finset.sum_singleton]
            simp_all only [↓reduceIte, Nat.reduceAdd, le_refl]
            apply Finset.not_mem_singleton.mpr
            intro h
            have : v ∈ {v} := Finset.mem_singleton_self v
            rw [← h] at this  -- `h : ∅ = {v}` を代入
            simp at this

          next h_1 =>
            simp_all only [Nat.cast_nonneg]

        case neg =>
          --このケースは頂点はrareにならない。bridgeを持たないので仮定に矛盾。
          exfalso
          dsimp [isBridgeFree] at h_bridge


      case neg =>
        have g_card : F.ground.card ≥ 2 := by
          search_proof
        let F' := F.trace v hv_ground h_ground_card'
        let F'_closure : ClosureSystem α := trace_closure_system F v hv_ground h_ground_card'
        have h_closure_ground : F'_closure.ground = F.ground \ {v} := by
          dsimp [F'_closure]
          dsimp [trace_closure_system]
          subst fgc
          simp_all only [Finset.card_erase_of_mem]
        -- F' の ground の要素数を n - 1 に縮小
        have h_ground_card' : F'_closure.ground.card = n - 1 := by
          rw [h_closure_ground]
          rw [Finset.card_erase_of_mem hv_ground]
        -- F' が rare vertex を持つことを示す
        let tpv := trace_bridge_vertex_rare F v hv_ground hv_bridge
        apply tpv.mpr
        have : n - 1 < n := by
          apply Nat.sub_lt_self
          exact h_ground_card'
        let ihn := ih (n-1) this
        dsimp [P_Bridge] at ihn
        let ihnf := ihn F'_closure h_ground_card'
        rw [h_closure_ground] at ihnf
        exact ihnf
      -/
    · sorry
