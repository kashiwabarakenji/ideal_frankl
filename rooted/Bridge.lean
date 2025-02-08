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

--xはsubtype。頂点がブリッジであることと、根付き集合のステムが空であることの関係。
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
    · dsimp [RS]
      dsimp [rootedSetsFromSetFamily]
      dsimp[rootedSetsSF]
      dsimp [allCompatiblePairs]
      dsimp [isCompatible]
      simp
      use v.stem
      use v.root
      constructor
      · simp
      · constructor
        · dsimp [allPairs]
          --rw [Finset.product]
          simp
          --apply Finset.mem_product.mpr
          constructor
          · simp_all only [Finset.empty_subset, RS, v]

          · simp_all only [Finset.coe_mem, v, RS]
        · constructor
          · simp_all only [not_false_eq_true, v, RS]
          · intro h
            intro t a
            rename_i h_1
            simp_all only [Finset.empty_subset, v, RS]
            obtain ⟨val, property⟩ := x
            simp_all only [RS]
            apply h_1
            simp_all only [RS]

    · simp_all only [and_self, v, RS]

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

--bridgeのtraceをしてもdegreeが変化しないことの補題
lemma trace_bridge_keep_degree (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (geq2: SF.ground.card ≥ 2) (x:SF.ground):
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
          simp_all only [ne_eq, Finset.mem_filter,Finset.mem_erase, not_false_eq_true, true_and]
        simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp, Finset.mem_erase]

    · intro hh
      by_cases y = x.val
      case pos =>
        dsimp [S] at ha1
        rw [Finset.mem_filter] at ha1
        have : y ∈ a1 := by
          rename_i h_1
          subst h_1
          simp_all only [Finset.mem_filter, Finset.mem_powerset, and_imp]
        exact this
      case neg =>
        have: y ∈ a2.erase x.val := by
          rw [@Finset.mem_erase]
          simp_all only [and_imp, ne_eq, not_false_eq_true, and_self, ii, S]
        have: y ∈ a1.erase x.val := by
          simp_all only [and_imp, Finset.mem_erase, ne_eq, not_false_eq_true,true_and, and_self]
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
        · simp_all only [Finset.mem_filter, Finset.mem_powerset, and_self, and_imp, subset_refl, Finset.coe_mem]
        ·
          simp_all only [ne_eq, Finset.mem_filter, Finset.mem_powerset, and_self, implies_true, and_imp, subset_refl]
          obtain ⟨val, property⟩ := x
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
          Finset.singleton_subset_iff, Finset.coe_mem]
        obtain ⟨val, property⟩ := x
        have : ¬ SF.sets b :=
        by
          simp_all only [subset_refl, implies_true, ne_eq, Finset.singleton_subset_iff]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [subset_refl, not_true_eq_false]
        have :SF.sets (b ∪ {val}):=
        by
          simp_all only [subset_refl, implies_true, ne_eq, Finset.singleton_subset_iff, false_or]
        have : b ∪ {val} = insert val b := by
          obtain ⟨val_1, property_1⟩ := y
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

    simp_all only [Finset.mem_filter,  Finset.coe_mem, Nat.cast_inj,  ii]
    simp_all only [ne_eq, subset_refl, implies_true, Finset.singleton_subset_iff, Finset.coe_mem,
      Finset.erase_insert_eq_erase, not_false_eq_true, Finset.erase_eq_of_not_mem,
      Finset.mem_insert, or_true, and_self, exists_const]

  have card_eq: S.card = S'.card := by
    apply @Finset.card_bij _ _ S S' ii hi2 inj surj

  dsimp [SetFamily.degree, SetFamily.trace]
  simp
  dsimp [S,S'] at card_eq
  convert card_eq

  --bridgeの次数は、すべてのhyperedgeの数と等しいという補題。あとで、bridgeがrareにならないという補題bridge_is_not_rareで使う。
  lemma bridge_degree (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (x:SF.ground):
    SF.is_bridge x →
    SF.degree x = SF.number_of_hyperedges :=
  by
    intro h_br
    simp_all only [SetFamily.degree, SetFamily.number_of_hyperedges, SetFamily.trace]
    obtain ⟨val, property⟩ := x
    simp_all only
    congr
    ext x : 2
    simp_all only [and_iff_left_iff_imp]
    intro a
    exact h_br _ a

--bridgeの頂点はrareにはならない補題。bridge_degreeというdegreeとnumber_of_hyperedgesが等しいという補題を使っている。この補題自体は使われていない。
lemma bridge_is_not_rare (SF: ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (x:SF.ground):
  SF.is_bridge x → ¬ SF.is_rare x :=
by
  intro h
  intro h_rare
  have h_deg := bridge_degree SF  x h
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
    · simp
    · constructor
      · exact SF.has_ground
      · exact Finset.coe_mem x

  simp_all only [gt_iff_lt, mul_le_iff_le_one_right, Nat.not_ofNat_le_one]

  --bridgeをtraceしても、x以外の頂点yがrare vertexかどうかは、変わらないという補題。
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

--すべてのhyperedgeの共通部分を与える関数。
def minimal_set (SF : ClosureSystem α) [DecidablePred SF.sets] : Finset α :=
  finsetIntersection (SF.ground.powerset.filter (fun s => SF.sets s))

--補題。閉集合族にとって、minimal_setはbridgeを与える関数ともいえる。
lemma bridge_lemma (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (x:SF.ground):
  SF.is_bridge x ↔ x.val ∈ (minimal_set SF) :=
by
  apply Iff.intro
  · intro h
    dsimp [minimal_set]
    dsimp [finsetIntersection]
    dsimp [SetFamily.is_bridge] at h
    simp
    constructor
    · use SF.ground
      constructor
      · constructor
        · simp
        · exact SF.has_ground
      · exact x.property
    · intro s hs
      intro sfs
      simp_all only

  · intro h
    dsimp [minimal_set] at h
    dsimp [finsetIntersection] at h
    simp at h
    dsimp [SetFamily.is_bridge]
    intro s hs
    have : s ⊆ SF.ground := by
      exact SF.inc_ground s hs
    exact h.2 s this hs

--全体集合しかない閉集合族.すべての点がbridgeといってもいい。一般的なフランクルの予想の前提として考えられる。のちに空集合を仮定するだけで十分であることが示される。
def is_trivial (SF : ClosureSystem α) [DecidablePred SF.sets]  : Prop :=
  SF.number_of_hyperedges = 1

--trivialでないときは、全体集合以外にもhyperedgeがある。必要十分条件。数学的には自明なのでテクニカルな補題と言える。
lemma trivial_lemma (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  ¬is_trivial SF ↔ ∃ s, SF.sets s ∧ s ≠ SF.ground :=
by
  apply Iff.intro
  · intro h
    by_contra h_contra
    simp at h_contra
    apply h
    dsimp [is_trivial]
    dsimp [SetFamily.number_of_hyperedges]
    simp_all only [Nat.cast_eq_one]
    have : Finset.filter (fun s => SF.sets s) SF.ground.powerset = {SF.ground} :=
    by
      apply Finset.ext
      intro s
      apply Iff.intro
      · intro h
        rw [Finset.mem_singleton]
        rw [Finset.mem_filter] at h
        simp_all only [Finset.mem_powerset, and_self]
        obtain ⟨left, right⟩ := h
        simp_all only [SF.has_ground]
      · intro h
        rw [Finset.mem_singleton] at h
        rw [Finset.mem_filter]
        simp_all only [Finset.mem_powerset, and_self]
        constructor
        ·
          subst h
          simp_all only [subset_refl]
        · exact SF.has_ground
    rw [this]
    simp
  · intro h
    obtain ⟨s, hs⟩ := h
    dsimp [is_trivial]
    dsimp [SetFamily.number_of_hyperedges]
    have inc: {s, SF.ground} ⊆ Finset.filter (fun s => SF.sets s) SF.ground.powerset :=
    by
      intro x
      intro h
      rw [Finset.mem_insert] at h
      cases h
      ·
        rw [Finset.mem_filter]
        simp_all only [Finset.mem_powerset, and_self]
        simp
        exact SF.inc_ground s hs.1
      ·
        simp_all only [ne_eq, Finset.mem_singleton, Finset.mem_filter, Finset.mem_powerset, subset_refl, true_and]
        exact SF.has_ground
    have eq2: ({s, SF.ground}:Finset (Finset α)).card = 2 :=
    by
      simp_all only [ne_eq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
        Finset.card_singleton, Nat.reduceAdd]
    have : (Finset.filter (fun s => SF.sets s) SF.ground.powerset).card ≥ 2 :=
    by
      let fcl := Finset.card_le_card inc
      simp_all only [ge_iff_le]
      convert fcl
      exact eq2.symm
    simp_all only [ne_eq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
      Finset.card_singleton, Nat.reduceAdd, ge_iff_le, Nat.cast_eq_one]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [Nat.not_ofNat_le_one]

--補題：空集合を持つことと、すべてのhyperedgeの共通部分が空集合であることが同値。
lemma minimal_set_lemma (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  SF.has_empty ↔ (minimal_set SF) = ∅ :=
by
  apply Iff.intro
  · intro h
    dsimp [minimal_set]
    by_contra h_contra
    apply Finset.nonempty_iff_ne_empty.mpr at h_contra
    obtain ⟨v, hv⟩ := h_contra
    dsimp [ClosureSystem.has_empty] at h
    dsimp [finsetIntersection] at hv
    simp at hv
    let hv2 := hv.2 ∅
    simp at hv2
    contradiction

  · intro h
    have : (SF.ground.powerset.filter (fun s => SF.sets s)).Nonempty :=
    by
      use SF.ground
      rw [Finset.mem_filter]
      constructor
      ·simp
      · exact SF.has_ground
    let fic := finite_intersection_in_closureSystem SF (SF.ground.powerset.filter (fun s => SF.sets s)) this
    have :(∀ T ∈ Finset.filter (fun s => SF.sets s) SF.ground.powerset, SF.sets T) :=
    by
      intro T
      intro hT
      rw [Finset.mem_filter] at hT
      exact hT.2
    specialize fic this
    dsimp [minimal_set] at h
    rw [h] at fic
    dsimp [ClosureSystem.has_empty]
    exact fic

--定理： 閉集合族は、空集合を持つことと、bridgeを持たないことが同値である。
lemma has_empty_theorem (SF: ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  SF.has_empty ↔ (∀ v, v ∈ SF.ground → ¬ SF.is_bridge v) :=
by
  constructor
  · intro h
    intro v
    intro h_v
    intro h_br
    dsimp [SetFamily.is_bridge] at h_br
    dsimp [ClosureSystem.has_empty] at h
    specialize h_br ∅
    simp_all only [Finset.not_mem_empty, imp_false, not_true_eq_false]
  · intro h
    dsimp [SetFamily.is_bridge] at h
    simp at h

    apply (minimal_set_lemma SF ).mpr
    dsimp [minimal_set]
    dsimp [finsetIntersection]
    by_contra h_contra
    simp at h_contra
    apply Finset.nonempty_iff_ne_empty.mpr at h_contra
    obtain ⟨v, hv⟩ := h_contra
    have : v ∈ SF.ground :=
    by
      simp_all only [Finset.mem_filter, Finset.mem_sup, Finset.mem_powerset, id_eq, subset_refl]
      obtain ⟨left, right⟩ := hv
      obtain ⟨w, h_1⟩ := left
      obtain ⟨left, right_1⟩ := h_1
      obtain ⟨left, right_2⟩ := left
      apply left
      simp_all only
    specialize h v this
    rw [Finset.mem_filter] at hv
    simp at hv
    obtain ⟨s,hs⟩ := h
    let fx := hv.2 s
    have : s ⊆ SF.ground:=
    by
      exact SF.inc_ground s hs.1
    specialize fx this
    exact hs.2 (fx hs.1)

--上の補題を対偶の形にしたもの。このほうが使いやすい。
lemma has_empty_theorem2 (SF: ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  ¬ SF.has_empty ↔ ∃ v, v ∈ SF.ground ∧ SF.is_bridge v :=
by
  apply Iff.intro
  · intro h
    contrapose! h
    apply (has_empty_theorem SF).mpr
    exact h
  · intro h
    contrapose! h
    apply (has_empty_theorem SF).mp
    exact h

--補題：閉集合族が空集合を持つならば、nontrivialである。
lemma has_empty_is_nontrivial (SF: ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  SF.has_empty → ¬ is_trivial SF :=
by
  intro h
  intro h_trivial
  have h_bridge := has_empty_theorem SF
  dsimp [ClosureSystem.has_empty] at h
  dsimp [is_trivial] at h_trivial

  have h_empty: ∅ ∈ Finset.filter (fun s => SF.sets s) SF.ground.powerset := by
    rw [Finset.mem_filter]
    constructor
    · simp
    · exact h
  have h_ground:SF.ground ∈ Finset.filter (fun s => SF.sets s) SF.ground.powerset := by
    rw [Finset.mem_filter]
    constructor
    · simp
    · exact SF.has_ground
  have inc: ({(∅:Finset α), SF.ground}:Finset (Finset α)) ⊆ Finset.filter (fun s => SF.sets s) SF.ground.powerset :=
  by
    simp_all only [Nat.cast_eq_one, ne_eq, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, and_self,
      subset_refl, true_and]
    intro v hv
    simp_all only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_powerset]
    cases hv with
    | inl h_1 =>
      subst h_1
      simp_all only [Finset.empty_subset, and_self]
    | inr h_2 =>
      subst h_2
      simp_all only [subset_refl, and_self]
  have : SF.ground ≠ ∅ := by
    let sfn := SF.nonempty_ground
    rw [Finset.nonempty_iff_ne_empty] at sfn
    exact sfn
  dsimp [SetFamily.number_of_hyperedges] at h_trivial
  have : ({(∅:Finset α), SF.ground}:Finset (Finset α)).card = 2 := by
    simp_all only [Nat.cast_eq_one, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, and_self,
      subset_refl, true_and, ne_eq]
    rw [Finset.card_insert_of_not_mem]
    · simp_all only [Finset.card_singleton, Nat.reduceAdd]
    · simp_all only [Finset.mem_singleton]
      apply Aesop.BuiltinRules.not_intro
      intro a
      simp_all only [Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.singleton_subset_iff, Finset.mem_filter,
        Finset.mem_powerset, subset_refl, and_self, not_true_eq_false]
  have :(Finset.filter (fun s => SF.sets s) SF.ground.powerset).card ≥ 2:= by
    let fcl := Finset.card_le_card inc
    simp_all only [Nat.cast_eq_one, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, and_self,
      subset_refl, true_and, ne_eq, ge_iff_le, Nat.not_ofNat_le_one]
    omega
  simp_all only [Nat.cast_eq_one, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, and_self, subset_refl,
    true_and, ne_eq, ge_iff_le, Nat.not_ofNat_le_one]



--nontrivialな閉集合族のbridgeをtraceした後のnontrivialityを示す。
lemma bridge_trace_nontrivial (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (geq2: SF.ground.card ≥ 2) (x:SF.ground):
  SF.is_bridge x →
  ¬is_trivial SF → ¬is_trivial (trace_closure_system SF x.val x.property geq2) :=
by
  intro h_br
  intro h_trivial
  intro h_trivial2
  let SF' := (trace_closure_system SF x.val x.property geq2)
  --もともとtrivialでないことからxの次数は2以上。よって、xを通る全体集合以外のhyperedge ssが存在する。
  --ss - xは、trace後のhyperedgeであり、これは全体集合ではない。
  --よって、traceは、2つ以上のhyperedgeを含むので、trivialでない。
  obtain ⟨ss, hss⟩ := (trivial_lemma SF).mp h_trivial
  let newss := ss.erase x.val
  have h_newss: (trace_closure_system SF x.val x.property geq2).sets newss := by
    dsimp [trace_closure_system]
    constructor
    ·
      simp_all only [ne_eq, Finset.mem_erase, not_true_eq_false, false_and, not_false_eq_true, newss]
    · right
      have: ss = newss ∪ {x.val} := by
        ext a : 1
        simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, Finset.mem_singleton, Finset.mem_insert]
        apply Iff.intro
        · intro a_1
          by_cases a = x.val
          case pos =>
            simp_all only [not_true_eq_false, and_true, or_true]
          case neg =>
            simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self, or_false, newss]
        · intro a_1
          simp_all only [Finset.mem_erase, ne_eq, newss]
          cases a_1 with
          | inl h => simp_all only
          | inr h_1 =>
            subst h_1
            apply h_br
            simp_all only
      rw [←this]
      exact hss.1

  have inc: ss ⊆ SF.ground := by
      exact SF.inc_ground ss hss.1

  have yexists: ∃ y:α, x.val ≠ y ∧ y ∈ SF.ground ∧ y ∉ ss := by
    have ne: ¬SF.ground ⊆ ss := by
      intro h
      have :SF.ground = ss := by
        exact Finset.Subset.antisymm h inc
      exact hss.2 this.symm

    obtain ⟨y, hyB, hyA⟩ := Finset.exists_of_ssubset ⟨inc, ne⟩
    use y

    constructor
    · --x.val ∈ ssで、y ∉ ssなので、x.val ≠ y
      intro h
      subst h
      dsimp [SetFamily.is_bridge] at h_br
      exact hyA (h_br ss hss.1)
    · simp_all only [ne_eq, not_false_eq_true, and_self, newss]

  obtain ⟨y, hy⟩ := yexists

  have SF'ground: SF'.ground = SF.ground.erase x.val := by
    dsimp [trace_closure_system]
    simp_all only [ne_eq, newss, SF']
    obtain ⟨val, property⟩ := x
    obtain ⟨left, right⟩ := hss
    simp_all only
    rfl

  have h_newss2: newss ≠ SF'.ground := by
    intro h
    --x.valでなくて、y ¥not newssをつかって違いを示す。
    have: y ∉ newss:= by
      dsimp [newss]
      intro hy
      rw [@Finset.mem_erase] at hy
      simp_all only [ne_eq, not_true_eq_false, and_false, SF', newss]
    simp_all only [ne_eq, Finset.mem_erase, and_true, Decidable.not_not, not_true_eq_false, Finset.coe_mem, true_and,
      false_and]

  have newssin: newss ∈ Finset.filter (fun s => SF'.sets s) SF'.ground.powerset := by
    rw [SF'ground]
    rw [Finset.mem_filter]
    constructor
    ·
      simp_all only [Finset.mem_powerset, subset_refl]
      dsimp [newss]
      intro x hx
      simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
      obtain ⟨left_3, right_2⟩ := hx
      exact inc right_2

    ·
      simp_all only [ne_eq, SF', newss]

  have SF'in : SF'.ground ∈ Finset.filter (fun s => SF'.sets s) SF'.ground.powerset := by
    rw [Finset.mem_filter]
    constructor
    ·
      simp_all only [Finset.mem_powerset, subset_refl]
    ·
      simp_all only [ne_eq, SF', newss]
      dsimp [trace_closure_system]
      constructor
      ·
        simp_all only [ne_eq, Finset.mem_erase, not_true_eq_false, false_and, not_false_eq_true, newss]
      · right
        have: SF.ground = SF.ground.erase ↑x ∪ {↑x} := by
          ext a : 1
          simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, Finset.mem_singleton, Finset.mem_insert]
          apply Iff.intro
          · intro a_1
            by_cases a = x.val
            case pos =>
              simp_all only [not_true_eq_false, and_true, or_true]
            case neg =>
              simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self, or_false, newss]
          · intro a_1
            simp_all only [Finset.mem_filter, Finset.mem_powerset, and_true, SF', newss]
            obtain ⟨val, property⟩ := x
            cases a_1 with
            | inl h => simp_all only
            | inr h_1 =>
              simp_all only
        rw [←this]
        exact SF.has_ground

  have h_newss3: {newss,SF'.ground} ⊆ Finset.filter (fun s => SF'.sets s) SF'.ground.powerset := by
    intro x hx
    simp_all only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_powerset]
    cases hx with
    | inl h =>
      simp_all only [and_self]
    | inr h_1 =>
      simp_all only [subset_refl, and_self]

  have : ({newss, SF'.ground}:Finset (Finset α)).card = 2 := by
    simp_all only [ne_eq, Finset.mem_filter, Finset.mem_powerset, and_true, subset_refl, true_and, Finset.mem_singleton,
      not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton, Nat.reduceAdd, SF', newss]

  have : (Finset.filter (fun s => SF'.sets s) SF'.ground.powerset).card ≥ 2 := by
    let fcl := Finset.card_le_card h_newss3
    simp_all only [ge_iff_le]
    convert fcl
    exact this.symm

  have : SF'.number_of_hyperedges ≥ 2 := by
    dsimp [SetFamily.number_of_hyperedges]
    simp_all only [ne_eq, Finset.mem_filter, Finset.mem_powerset, and_true, subset_refl, true_and,
      Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
      ge_iff_le, Nat.ofNat_le_cast, SF', newss]
  dsimp [is_trivial] at h_trivial2
  simp_all only [ne_eq, Finset.mem_filter, Finset.mem_powerset, and_true, subset_refl, true_and,
    Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
    ge_iff_le, Nat.not_ofNat_le_one, SF', newss]

def P_nontrivial {α : Type} [DecidableEq α] [Fintype α] (n : Nat) : Prop :=
   (∀ (F : ClosureSystem α) [DecidablePred F.sets], F.ground.card = n → ¬ is_trivial F → ∃v, v ∈ F.ground ∧ F.is_rare v)

def P_has_empty {α : Type} [DecidableEq α] [Fintype α] (n : Nat) : Prop :=
   (∀ (F : ClosureSystem α) [DecidablePred F.sets], F.ground.card = n → F.has_empty → ∃ (v : α), v ∈ F.ground ∧ F.is_rare v)

--定理： nontrivialな閉集合族に対してrare vertexが存在することと、空集合持つ集合族でrare vertexを持つことが同値。
theorem bridge_free_theorem {α : Type} [Infinite α] [Fintype α] [DecidableEq α] :
  (∀ (n : Nat), @P_nontrivial α _ _ n) ↔ (∀ (n : Nat), @P_has_empty α _ _ n) :=
by
  apply Iff.intro
  · -- 簡単な方向。nontrivialな任意の集合族にrareなvertexが存在するので、
    dsimp [P_nontrivial,P_has_empty]
    intro h --bridgeを持つ場合の仮定
    intro n
    intro F inst_1 a a_1
    have :¬is_trivial F := by
      exact has_empty_is_nontrivial F a_1
    obtain ⟨v, hv_ground, hv_rare⟩ := h n F a this
    use v

  · -- 帰納法による方向: emptyに対する予想を仮定して、一般の場合を示す。
    intro h
    intro n
    dsimp [P_has_empty] at h
    dsimp [P_nontrivial]
    apply @Nat.strong_induction_on (λ n => ∀ (F : ClosureSystem α) [DecidablePred F.sets], F.ground.card = n → ¬is_trivial F → ∃ v ∈ F.ground, F.is_rare v)

    intro n ih F inst_1 h_size h_trivial
    --emptyを持つ場合と持たない場合に分ける。
    by_cases h_bridge : F.has_empty
    case pos =>
      have h_ground_card : F.ground.card = n := by
        exact h_size
      have h_trivial : ¬is_trivial F := by
        exact h_trivial
      obtain ⟨v, hv_ground, hv_rare⟩ := h n F h_ground_card h_bridge
      use v

    case neg => --emptyを持たない場合。帰納法を使って証明


      -- F が Bridge を持つ場合、Bridge を削除して帰納仮定を適用
      dsimp [ClosureSystem.has_empty] at h_bridge

      have h_ground_card' : F.ground.card ≥ 1 := by
        convert F.nonempty_ground
        subst h_size
        simp_all only [ge_iff_le, Finset.one_le_card]
      by_cases gc: F.ground.card = 1
      case pos => --台集合の大きさが1のとき

        dsimp [SetFamily.is_rare]
        -- 台集合が1(gc)で、空集合を持たない(h_bridge)ということは、全体集合だけ。
        -- このケースはtrivialになることを示す。
        dsimp [is_trivial] at h_trivial

        rw [Finset.card_eq_one] at gc
        obtain ⟨vv, h_vv⟩ := gc
        use vv
        constructor
        subst h_size
        simp_all only [and_true, Finset.mem_singleton, Finset.card_singleton, ge_iff_le, le_refl, Nat.lt_one_iff,
          forall_eq]
        simp
        have pow: ({vv}:Finset α).powerset = {∅, {vv}} := by
          ext a : 1
          simp_all only [Finset.mem_powerset, Finset.mem_singleton, Finset.mem_insert, Finset.mem_singleton]
          apply Iff.intro
          · intro a_1
            subst h_size
            simp_all only [and_true, Finset.subset_singleton_iff, Finset.card_singleton, Nat.lt_one_iff, forall_eq,
              ge_iff_le, le_refl]
          · intro a_1
            cases a_1 with
            | inl h =>
              subst h_size  h
              simp_all only [and_true, Finset.card_singleton, Nat.lt_one_iff, forall_eq, ge_iff_le, le_refl,
                Finset.subset_singleton_iff, true_or]
            | inr h_1 =>
              subst h_1
              subst h_size
              simp_all only [and_true, Finset.card_singleton, Nat.lt_one_iff, forall_eq, ge_iff_le, le_refl,
                subset_refl]

        have : F.number_of_hyperedges = 1 := by
          dsimp [SetFamily.number_of_hyperedges]
          rw [h_vv]
          rw [pow]
          rw [@Finset.card_filter]
          rw [Finset.sum_insert]
          rw [Finset.sum_singleton]
          simp
          subst h_size
          --((if F.sets ∅ then 1 else 0) + if F.sets {vv} then 1 else 0) = 1を示せばいいが、
          -- h_bridgeよりF.sets ∅ = falseであり、F.has_groundより、F.sets {vv} = trueである。
          have h0 : F.sets {vv} :=
          by
            rw [←h_vv]
            exact F.has_ground
          simp_all only [Finset.card_singleton, ge_iff_le, le_refl]
          have h1 : (if F.sets ∅ then 1 else 0) = 0 := by simp [h_bridge]
          have h2 : (if F.sets {vv} then 1 else 0) = 1 := by simp [h0]
          simp
          show ∅ ∉ {{vv}}
          rw [Finset.mem_singleton]
          exact ne_of_beq_false rfl
        simp_all only [ge_iff_le, Nat.ofNat_le_cast]
        subst h_size
        simp_all only [not_true_eq_false]

      case neg =>
        have g_card : F.ground.card ≥ 2 := by
          subst h_size
          simp_all only [ge_iff_le, Finset.one_le_card]
          apply Nat.succ_le_of_lt
          have h : F.ground.card > 1 :=
          by
            apply Nat.lt_iff_le_and_ne.mpr
            constructor
            simp_all only [Finset.one_le_card]

            simp_all only [ne_eq]
            apply Aesop.BuiltinRules.not_intro
            intro a
            simp_all only [not_true_eq_false]
          simp_all only [gt_iff_lt]

        --emptyを持たない場合は、bridgeを持つので、そのひとつを取り出して、vとする。
        obtain ⟨v, hv⟩ := (has_empty_theorem2 F ).mp h_bridge

        --let F' := F.trace v hv.1 g_card
        let F'_closure : ClosureSystem α := trace_closure_system F v hv.1 g_card
        let h_closure_ground : F'_closure.ground = F.ground \ {v} := by
          dsimp [F'_closure]
          dsimp [trace_closure_system]
          subst h_size
          simp_all only [ge_iff_le, Finset.one_le_card, F'_closure]
          obtain ⟨left, right⟩ := hv
          ext a : 1
          simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
          apply Iff.intro
          · intro a_1
            simp_all only [not_false_eq_true, and_self]
          · intro a_1
            simp_all only [not_false_eq_true, and_self]
        -- F' の ground の要素数を n - 1 に縮小
        have h_ground_card' : F'_closure.ground.card = n - 1 := by
          rw [h_closure_ground]
          let fc := Finset.card_erase_of_mem hv.1
          have :F.ground \ {v} = F.ground.erase v := by
            rw [Finset.erase_eq]
          simp_all only [ge_iff_le, Finset.one_le_card, Finset.card_erase_of_mem, F'_closure]

        -- [方針] F' が rare vertex を持つことを示す。
        --まず、ihを使って、帰納法の仮定によりtraceした集合族にrareな頂点が存在していることを示す。
        --そのあとに、trace_bridge_rareを使って、bridgeをtraceする前でもその頂点はrareであることを示す。
        have h_trivial'  :¬is_trivial F'_closure := by
          intro h_trivial'
          --bridgeをtraceしたものも全体集合以外にもう1つ要素があることをいう補題を使う。
          let btn := bridge_trace_nontrivial F g_card ⟨v,hv.1⟩ hv.2 h_trivial
          subst h_size
          simp_all only [ge_iff_le, Finset.one_le_card, F'_closure, btn]

        have : n-1 < n := by
          subst h_size
          simp_all only [Finset.one_le_card, tsub_lt_self_iff, Finset.card_pos, Nat.lt_one_iff, and_self]--
        --帰納法の仮定でひとつ小さいものに対して、言明が成り立つことを使う。
        let iht := ih (n-1) this F'_closure h_ground_card' h_trivial'
        let tpv := trace_bridge_rare F g_card ⟨v,hv.1⟩ hv.2
        --v'がひとつ小さい集合でのrare vertex。
        obtain ⟨v', hv'⟩ := iht
        use v'
        have hv'': v' ∈ F.ground := by
            subst h_size
            simp_all only [ge_iff_le, Finset.one_le_card, tsub_lt_self_iff, pos_of_gt, and_self, F'_closure]
            rw [h_closure_ground] at hv'
            simp_all only [Finset.mem_sdiff, Finset.mem_singleton, F'_closure]
        constructor
        ·
          subst h_size
          simp_all only [ge_iff_le, Finset.one_le_card, tsub_lt_self_iff, Finset.card_pos, Nat.lt_one_iff, pos_of_gt,
            and_self, F'_closure]
        ·
          let tpvv := tpv ⟨v',hv''⟩
          show F.is_rare v'
          have vneq: v ≠ v' := by
            intro h
            subst h
            subst h_size
            simp_all only [ge_iff_le, Finset.one_le_card, tsub_lt_self_iff, Finset.card_pos, Nat.lt_one_iff,
              pos_of_gt, and_self, F'_closure]
            rw [h_closure_ground] at hv'
            simp_all only [Finset.mem_sdiff, Finset.mem_singleton, F'_closure]
            simp_all only [not_true_eq_false, and_false, false_and, F'_closure]
          refine (tpvv ?_).mpr hv'.2
          subst h_size
          simp_all only [ne_eq, tsub_lt_self_iff, Nat.lt_one_iff,pos_of_gt,  Subtype.mk.injEq, not_false_eq_true]
