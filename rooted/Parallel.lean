--Parallelな頂点に関すること。一部は、RootedImplicationと記述が被っている。
import Mathlib.Data.Nat.Defs
import rooted.ClosureMinors
import rooted.RootedImplication


open Classical

variable {α : Type} [Fintype α] [DecidableEq α]

--parallelの定義は、今のところimplicationのところにある。

lemma parallel_same_degree (SF: ClosureSystem α) [DecidablePred SF.sets] (x y:α) (p:parallel SF x y):
  SF.degree x = SF.degree y :=
by
  dsimp [SetFamily.degree]
  let S:= (Finset.filter (fun s => SF.sets s ∧ x ∈ s) SF.ground.powerset)
  let T:= (Finset.filter (fun s => SF.sets s ∧ y ∈ s) SF.ground.powerset)
  let i: {s // s ∈ S} → {s // s ∈ T} := fun s => ⟨s.val, by
    simp_all only [Finset.mem_filter, Finset.mem_powerset, T, S]
    obtain ⟨val, property⟩ := s
    dsimp [parallel] at p
    let p21 := p.2.2

    dsimp [S] at property
    rw [Finset.mem_filter] at property
    let p1 := property.1
    rw [Finset.mem_powerset] at p1
    let pv:= (p21 val property.2.1).mp property.2.2
    constructor
    · simp
      exact p1
    · constructor
      · simp
        exact property.2.1
      · simp
        exact pv
  ⟩
  let ii :  (a : { x // x ∈ S }) → a ∈ S.attach → { x // x ∈ T } := fun a ha => i a
  have hi: ∀ (a : { x // x ∈ S }) (ha : a ∈ S.attach), ii a ha ∈ T.attach :=
  by
    intro a ha
    simp_all only [Finset.mem_attach, T, ii, S, i]
  have inj : ∀ (a₁ : { x // x ∈ S }) (ha₁ : a₁ ∈ S.attach) (a₂ : { x // x ∈ S }) (ha₂ : a₂ ∈ S.attach),
    ii a₁ ha₁ = ii a₂ ha₂ → a₁ = a₂ :=
  by
    dsimp [S, T, i, ii]
    intro a₁ ha₁ a₂ ha₂ h
    simp_all
    obtain ⟨val, property⟩ := a₁
    obtain ⟨val_1, property_1⟩ := a₂
    subst h
    simp_all only
  have surj: ∀ b ∈ T.attach, ∃ a, ∃ (ha : a ∈ S.attach), ii a ha = b :=
  by
    dsimp [S, T, i, ii]
    dsimp [Finset.attach]
    intro b hb
    simp at hb
    rw [Multiset.attach] at hb
    simp at hb
    --obtain ⟨val, property⟩ := b
    --rw[Finset.mem_filter] at property
    simp
    --let p22:= property.2
    obtain ⟨val2, property2⟩ := hb
    obtain ⟨val, property⟩ := property2
    use val2
    constructor
    · simp_all only [Finset.mem_filter, Finset.mem_powerset]
      simp
      rw [Multiset.attach]
      simp
      constructor
      exact val.1
      constructor
      exact val.2.1
      dsimp [parallel] at p
      exact (p.2.2 val2 val.2.1).mpr val.2.2
    · constructor
      · exact val.1
      · constructor
        exact val.2.1
        dsimp [parallel] at p
        exact (p.2.2 val2 val.2.1).mpr val.2.2

  let bi:= @Finset.card_bij S T S.attach T.attach ii hi inj surj
  dsimp [S,T] at bi
  rw [Finset.card_attach] at bi
  rw [Finset.card_attach] at bi
  rw [bi]

lemma ground_card_ge_two (SF : ClosureSystem α)  [DecidablePred SF.sets]
  (x : α) (hx : x ∈ SF.ground) (p:(∃ y: α, x ≠ y ∧ parallel SF x y)) :
  SF.ground.card ≥ 2 :=
by
  obtain ⟨y, hy, h⟩ := p
  have xyinc: ({x,y}:Finset α) ⊆ SF.ground :=
  by
    have : y ∈ SF.ground := by
      dsimp only [parallel] at h
      exact (h.2.2 SF.ground SF.has_ground ).mp hx
    simp_all only [ne_eq]
    intro y' hy'
    simp_all only [Finset.mem_insert, Finset.mem_singleton]
    cases hy' with
    | inl h_1 =>
      subst h_1
      simp_all only
    | inr h_2 =>
      subst h_2
      simp_all only
  --使ってない模様。
  have _ : ({x, y}:Finset α).card = 2 := by
    simp_all only [ne_eq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
      Nat.reduceAdd]
  have:({x,y}:Finset α).card ≤ SF.ground.card := by
    exact Finset.card_le_card xyinc
  simp_all only [ne_eq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
    Nat.reduceAdd, ge_iff_le]

--パラレルの1つの頂点をtraceしても、hyperedgeの数は変わらない。4時間ぐらい。
lemma trace_paralel_vertex (SF: ClosureSystem α) [DecidablePred SF.sets] (x:α) (hx: x ∈ SF.ground):
  (p:(∃ y: α, x ≠ y ∧ parallel SF x y)) →
 SF.number_of_hyperedges = (SF.toSetFamily.trace x hx (ground_card_ge_two SF x hx p)).number_of_hyperedges :=
by
  intro p
  obtain ⟨w, h⟩ := p
  obtain ⟨left, right⟩ := h
  dsimp [SetFamily.trace]
  dsimp [SetFamily.number_of_hyperedges]
  simp
  let S:= (Finset.filter (fun s => SF.sets s) SF.ground.powerset)
  let T:= (Finset.filter (fun s => x ∉ s ∧ (SF.sets s ∨ SF.sets (s ∪ {x}))) (SF.ground.erase x).powerset)
  let i: {s // s ∈ S} → {s // s ∈ T} := fun s => ⟨(s.val.erase x), by
    simp_all only [ne_eq, Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, not_true_eq_false, false_and,
      not_false_eq_true, true_and, T, S]
    obtain ⟨val, property⟩ := s
    simp_all only --必要
    simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
    obtain ⟨left_1, right_1⟩ := property
    apply And.intro
    · show val.erase x ⊆ SF.ground.erase x
      intro y hy
      simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
      obtain ⟨left_2, right_2⟩ := hy
      exact left_1 right_2
    · by_cases h: x ∈ val
      · right
        have : val.erase x ∪ {x} = val := by
          ext a : 1
          simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, Finset.mem_singleton]
          apply Iff.intro
          · intro a_1
            cases a_1 with
            | inl h_1 => simp_all only
            | inr h_2 =>
              --subst h_2
              simp_all only
          · intro a_1
            simp_all only [and_true]
            tauto
        rw [this]
        exact right_1
      · left
        simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem]
  ⟩
  let ii :  (a : { x // x ∈ S }) → a ∈ S.attach → { x // x ∈ T } := fun a ha => i a

  have hi: ∀ (a : { x // x ∈ S }) (ha : a ∈ S.attach), ii a ha ∈ T.attach :=
  by
    intro a ha
    simp_all only [Finset.mem_attach, T, ii, S, i]
  have inj : (∀ (a₁ : { x // x ∈ S }) (ha₁ : a₁ ∈ S.attach) (a₂ : { x // x ∈ S }) (ha₂ : a₂ ∈ S.attach),
    ii a₁ ha₁ = ii a₂ ha₂ → a₁ = a₂) :=
  by
    dsimp [S, T, i, ii]
    intro a₁ ha₁ a₂ ha₂ h --hによって、x以外ではa₁とa₂が等しい。
    simp_all --必要
    dsimp [parallel] at right
    dsimp [S] at ii
    dsimp [Finset.attach] at ii
    by_cases hx: x ∈ a₁.val
    case pos =>
      have : w ∈ a₁.val := by
        obtain ⟨left_1, right⟩ := right
        obtain ⟨val, property⟩ := a₁
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
      have : w ∈ (a₁.val).erase x :=
      by
        rw [Finset.mem_erase]
        simp_all only [ne_eq, and_true]
        obtain ⟨left_1, right⟩ := right
        obtain ⟨val, property⟩ := a₁
        obtain ⟨left_2, right⟩ := right
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        contradiction
      have : w ∈ a₂.val := by
        rw [h] at this
        simp_all only [Finset.mem_erase, ne_eq]
      have h': x ∈ a₂.val:=
      by --xでも一致していることを示す。
        simp_all only [Finset.mem_erase, ne_eq, and_true]
        obtain ⟨val_1, property_1⟩ := a₂
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
      ext y
      apply Iff.intro
      · by_cases hy: y = x
        case pos =>
          intro a
          subst hy
          simp_all only [Finset.mem_erase, ne_eq, and_true]
        case neg =>
          have : a₁.val  = ((a₁.val).erase x)∪{x} := by
            ext a : 1
            apply Iff.intro
            · intro hh
              by_cases hh': a = x
              case pos =>
                subst hh'
                simp_all only
                simp_all only [Finset.mem_erase, ne_eq, and_true, Finset.mem_union, not_true_eq_false,
                  Finset.mem_singleton, or_true]
              case neg =>
                rw [Finset.mem_union]
                left
                rw [Finset.mem_erase]
                simp_all only [Finset.mem_erase, ne_eq, and_true, not_false_eq_true, and_self]
            · intro hh
              rw [Finset.mem_union] at hh
              cases hh with
              | inl h_1 =>
                rw [Finset.mem_erase] at h_1
                simp_all only [Finset.mem_erase, ne_eq, and_true, not_false_eq_true, and_self]
              | inr h_2 =>
                simp_all only [Finset.mem_erase, ne_eq, and_true, Finset.mem_singleton]
          rw [this]
          intro hh
          rw [Finset.mem_union] at hh
          cases hh with
          | inl h_1 => --このときは、xがyと一致しない時、
            rw [Finset.mem_erase] at h_1
            rw [h] at this
            have a2erase: a₂.val  = ((a₂.val).erase x)∪{x} := by
              simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
                Finset.mem_singleton, or_true, not_false_eq_true, or_false]
              obtain ⟨left_1, right⟩ := right
              obtain ⟨val, property⟩ := a₁
              simp_all only [not_false_eq_true, true_and, or_false, Finset.mem_filter, Finset.mem_powerset]
              ext a : 1
              simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, Finset.mem_singleton]
              apply Iff.intro
              · intro a_1
                simp_all only [and_true]
                tauto
              · intro a_1
                cases a_1 with
                | inl h_1 => simp_all only
                | inr h_2 =>
                  simp_all only
            rw [a2erase]
            rw [this] at h_1
            exact h_1.2
          | inr h_2 => --このときはxとyが一致するとき、
            have xeqy: x = y := by
              rw [Finset.mem_singleton] at h_2
              exact h_2.symm
            rw [←xeqy]
            exact h'
      · intro a  --by_cases hx: x ∈ a₁.valのposiの中。y ∈ ↑a₂ → y ∈ ↑a₁を示す。逆向きと同じ証明になる？
        simp_all only [Finset.mem_erase, ne_eq, and_true]
        obtain ⟨val, property⟩ := a₁
        obtain ⟨val_1, property_1⟩ := a₂
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        show y ∈ val
        --yがwと一致するかどうかで場合分け？
        by_cases hy: y = x
        case pos =>
          subst hy
          simp_all only [Finset.mem_erase, ne_eq, and_true]
        case neg =>
          --val.erase x = val_1.erase xを使うと、y ∈ val_1が目標。a : y ∈ val_1
          have : y ∈ val_1.erase x := by
            simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self]
          rw [←h] at this
          rw [Finset.mem_erase] at this
          exact this.2

    case neg => --x ∈ a₁.valでないとき、a₁ = a₂を示す。
      --(↑a₁).erase x = (↑a₂).erase xはわかっているので、 x ∉ a₁.valであることを示せばよい。
      --まず、wもa₁.valに含まれないことを示す。次にwは、a₂.valにも含まれず。xもa₂.valに含まれず。
      have : w ∉ a₁.val :=
      by --これはパラレルの条件、rightからわかる。
        obtain ⟨val, property⟩ := a₁
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem]
      have : w ∉ a₂.val :=
      by
        simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem, Finset.mem_erase, ne_eq, not_true_eq_false,
          false_and, not_and]
        obtain ⟨val, property⟩ := a₁
        obtain ⟨val_1, property_1⟩ := a₂
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [not_true_eq_false, imp_false, Decidable.not_not]
      have : x ∉ a₂.val :=
      by
        obtain ⟨val, property⟩ := a₁
        obtain ⟨val_1, property_1⟩ := a₂
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        simp_all only [Finset.mem_filter, Finset.mem_powerset, not_false_eq_true, Finset.erase_eq_of_not_mem,
          and_self]
      ext y
      apply Iff.intro
      ·
        intro a
        simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem]
      ·
        intro a
        simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem]

  have surj: ∀ b ∈ T.attach, ∃ a, ∃ (ha : a ∈ S.attach), ii a ha = b :=
  by
    dsimp [S, T, i, ii]
    dsimp [Finset.attach]
    intro b hb
    simp at hb
    rw [Multiset.attach] at hb
    simp at hb --hbのほうも分解した方がいいか。
    obtain ⟨val, property⟩ := b
    rw[Finset.mem_filter] at property
    simp
    let p22:= property.2.2
    cases p22 with
    | inl pl =>
      --∃ a, (∃ (x : a ⊆ SF.ground ∧ SF.sets a), ⟨a, ⋯⟩ ∈ (Multiset.filter (fun s => SF.sets s) SF.ground.powerset.val).attach) ∧ a.erase x = val
      have : val ⊆ SF.ground := by
        --obtain ⟨left, right⟩ := property
        exact SF.inc_ground val pl
      let tmp := And.intro this pl
      use val
      constructor
      ·
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        simp
        rw [Multiset.attach]
        simp
        constructor
        exact this
        exact pl
      · simp
        exact property.2.1
    | inr pr =>
      --∃ a, (∃ (x : x ∉ a ∧ (SF.sets a ∨ SF.sets (a ∪ {x}))), ⟨a, ⋯⟩ ∈ (Multiset.filter (fun s => x ∉ s ∧ (SF.sets s ∨ SF.sets (s ∪ {x}))) (SF.ground.erase x).powerset.val).attach) ∧ a.erase x = val
      have : val ∪ {x} ⊆ SF.ground := by
        --obtain ⟨left, right⟩ := property
        exact SF.inc_ground (val ∪ {x}) pr
      let tmp := And.intro this pr
      use val ∪ {x}
      constructor
      ·
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        simp
        rw [Multiset.attach]
        simp
        constructor
        exact this
        exact pr
      · let pr21 := property.2.1
        rw [Finset.union_comm]
        rw [←Finset.insert_eq x val]
        simp [Finset.erase_insert pr21]

  let bi:= @Finset.card_bij S T S.attach T.attach ii hi inj surj

  dsimp [S,T] at bi
  rw [Finset.card_attach] at bi
  rw [Finset.card_attach] at bi
  convert bi

--パラレルな頂点がある場合には、そのうち一つをtraceしても、traceした以外の頂点の次数が変わらない
--hyperedgeの数が変わらないことの証明と似ているが、違うので、その結果を利用したり、共通の補題を設けるよりも、直接証明した方が早い気がするので、直接証明する。
lemma trace_paralel_vertex_degree (SF: ClosureSystem α) [DecidablePred SF.sets] (x:α) (hx: x ∈ SF.ground) (z:α):
  (p:(∃ y: α, x ≠ y ∧ parallel SF x y)) → z ≠ x →
 SF.degree z = (SF.toSetFamily.trace x hx (ground_card_ge_two SF x hx p)).degree z:=
by
  intro p
  intro hzx
  obtain ⟨w, h⟩ := p
  obtain ⟨left, right⟩ := h
  dsimp [SetFamily.trace]
  dsimp [SetFamily.degree]
  let S:= (Finset.filter (fun s => SF.sets s ∧ z ∈ s) SF.ground.powerset)
  let T:= (Finset.filter (fun s => x ∉ s ∧ z ∈ s ∧ (SF.sets s ∨ SF.sets (s ∪ {x}))) (SF.ground.erase x).powerset)
  let i: {s // s ∈ S} → {s // s ∈ T} := fun s => ⟨(s.val.erase x), by
    simp_all only [ne_eq, Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase, not_true_eq_false, false_and,
      not_false_eq_true, true_and, T, S]
    obtain ⟨val, property⟩ := s
    simp_all only --必要
    simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
    obtain ⟨left_1, right_1⟩ := property
    apply And.intro
    · show val.erase x ⊆ SF.ground.erase x
      intro y hy
      simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
      obtain ⟨left_1, right_2⟩ := hy
      rename_i left_1_1
      exact left_1_1 right_2
    · by_cases h: x ∈ val
      · simp
        right
        have : val.erase x ∪ {x} = val := by
          ext a : 1
          simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, Finset.mem_singleton]
          apply Iff.intro
          · intro a_1
            cases a_1 with
            | inl h_1 => simp_all only
            | inr h_2 =>
              --subst h_2
              simp_all only
          · intro a_1
            simp_all only [and_true]
            tauto
        rw [this]
        simp_all only
      · simp
        left
        simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem]
  ⟩
  let ii :  (a : { x // x ∈ S }) → a ∈ S.attach → { x // x ∈ T } := fun a ha => i a

  have hi: ∀ (a : { x // x ∈ S }) (ha : a ∈ S.attach), ii a ha ∈ T.attach :=
  by
    intro a ha
    simp_all only [Finset.mem_attach, T, ii, S, i]
  have inj : ∀ (a₁ : { x // x ∈ S }) (ha₁ : a₁ ∈ S.attach) (a₂ : { x // x ∈ S }) (ha₂ : a₂ ∈ S.attach),
    ii a₁ ha₁ = ii a₂ ha₂ → a₁ = a₂ :=
  by
    dsimp [S, T, i, ii]
    intro a₁ ha₁ a₂ ha₂ h --hによって、x以外ではa₁とa₂が等しい。
    simp_all --必要
    dsimp [parallel] at right
    dsimp [S] at ii
    dsimp [Finset.attach] at ii
    by_cases hx: x ∈ a₁.val
    case pos =>
      have : w ∈ a₁.val := by
        obtain ⟨left_1, right⟩ := right
        obtain ⟨val, property⟩ := a₁
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
      have : w ∈ (a₁.val).erase x :=
      by
        rw [Finset.mem_erase]
        simp_all only [ne_eq, and_true]
        obtain ⟨left_1, right_2⟩ := right
        obtain ⟨val, property⟩ := a₁
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [not_false_eq_true, not_true_eq_false, implies_true, and_true]
      have : w ∈ a₂.val := by
        rw [h] at this
        simp_all only [Finset.mem_erase, ne_eq]
      have h': x ∈ a₂.val:=
      by --xでも一致していることを示す。
        simp_all only [Finset.mem_erase, ne_eq, and_true]
        obtain ⟨val_1, property_1⟩ := a₂
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
      ext y
      apply Iff.intro
      · by_cases hy: y = x
        case pos =>
          intro a
          subst hy
          simp_all only [Finset.mem_erase, ne_eq, and_true]
        case neg =>
          have : a₁.val  = ((a₁.val).erase x)∪{x} := by
            ext a : 1
            apply Iff.intro
            · intro hh
              by_cases hh': a = x
              case pos =>
                subst hh'
                simp_all only
                simp_all only [not_false_eq_true, Finset.mem_erase, ne_eq, and_true, Finset.mem_union,
                  not_true_eq_false, Finset.mem_singleton, or_true]
              case neg =>
                rw [Finset.mem_union]
                left
                rw [Finset.mem_erase]
                simp_all only [Finset.mem_erase, ne_eq, and_true, not_false_eq_true, and_self]
            · intro hh
              rw [Finset.mem_union] at hh
              cases hh with
              | inl h_1 =>
                rw [Finset.mem_erase] at h_1
                simp_all only [Finset.mem_erase, ne_eq, and_true, not_false_eq_true, and_self]
              | inr h_2 =>
                simp_all only [Finset.mem_erase, ne_eq, and_true, Finset.mem_singleton]
          rw [this]
          intro hh
          rw [Finset.mem_union] at hh
          cases hh with
          | inl h_1 => --このときは、xがyと一致しない時、
            rw [Finset.mem_erase] at h_1
            rw [h] at this
            have a2erase: a₂.val  = ((a₂.val).erase x)∪{x} := by
              simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
                Finset.mem_singleton, or_true, not_false_eq_true, or_false]
              obtain ⟨left_1, right⟩ := right
              obtain ⟨val, property⟩ := a₁
              simp_all only [not_false_eq_true, true_and, or_false, Finset.mem_filter, Finset.mem_powerset]
              ext a : 1
              simp_all only [Finset.mem_union, Finset.mem_erase, ne_eq, Finset.mem_singleton]
              apply Iff.intro
              · intro a_1
                simp_all only [and_true]
                tauto
              · intro a_1
                cases a_1 with
                | inl h_1 => simp_all only
                | inr h_2 =>
                  simp_all only
            rw [a2erase]
            rw [this] at h_1
            exact h_1.2
          | inr h_2 => --このときはxとyが一致するとき、
            have xeqy: x = y := by
              rw [Finset.mem_singleton] at h_2
              exact h_2.symm
            rw [←xeqy]
            exact h'
      · intro a  --by_cases hx: x ∈ a₁.valのposiの中。y ∈ ↑a₂ → y ∈ ↑a₁を示す。逆向きと同じ証明になる？
        simp_all only [Finset.mem_erase, ne_eq, and_true]
        obtain ⟨val, property⟩ := a₁
        obtain ⟨val_1, property_1⟩ := a₂
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        show y ∈ val
        --yがwと一致するかどうかで場合分け？
        by_cases hy: y = x
        case pos =>
          subst hy
          simp_all only [Finset.mem_erase, ne_eq, and_true]
        case neg =>
          --val.erase x = val_1.erase xを使うと、y ∈ val_1が目標。a : y ∈ val_1
          have : y ∈ val_1.erase x := by
            simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self]
          rw [←h] at this
          rw [Finset.mem_erase] at this
          exact this.2
    case neg =>
      have : w ∉ a₁.val :=
      by --これはパラレルの条件、rightからわかる。
        obtain ⟨val, property⟩ := a₁
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem]
      have : w ∉ a₂.val :=
      by
        simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem, Finset.mem_erase, ne_eq, not_true_eq_false,
          false_and, not_and]
        obtain ⟨val, property⟩ := a₁
        obtain ⟨val_1, property_1⟩ := a₂
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [not_true_eq_false, imp_false, Decidable.not_not]
      have : x ∉ a₂.val :=
      by
        obtain ⟨val, property⟩ := a₁
        obtain ⟨val_1, property_1⟩ := a₂
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        simp_all only [Finset.mem_filter, Finset.mem_powerset, not_false_eq_true, Finset.erase_eq_of_not_mem,
          and_self]
      ext y
      apply Iff.intro
      ·
        intro a
        simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem]
      ·
        intro a
        simp_all only [not_false_eq_true, Finset.erase_eq_of_not_mem]

  have surj: ∀ b ∈ T.attach, ∃ a, ∃ (ha : a ∈ S.attach), ii a ha = b :=
  by
    dsimp [S, T, i, ii]
    dsimp [Finset.attach]
    intro b hb
    --simp at hb --hbは使ってない。
    --rw [Multiset.attach] at hb
    --simp at hb
    obtain ⟨val, property⟩ := b
    rw[Finset.mem_filter] at property
    simp
    let p22:= property.2.2.2
    cases p22 with
    | inl pl =>
      --∃ a, (∃ (x : a ⊆ SF.ground ∧ SF.sets a), ⟨a, ⋯⟩ ∈ (Multiset.filter (fun s => SF.sets s) SF.ground.powerset.val).attach) ∧ a.erase x = val
      have : val ⊆ SF.ground := by
        --obtain ⟨left, right⟩ := property
        exact SF.inc_ground val pl
      let tmp := And.intro this pl
      use val
      constructor
      ·
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        simp
        rw [Multiset.attach]
        simp
        constructor
        exact this
        constructor
        exact pl
        exact property.2.2.1
      · simp
        exact property.2.1
    | inr pr =>
      --∃ a, (∃ (x : x ∉ a ∧ (SF.sets a ∨ SF.sets (a ∪ {x}))), ⟨a, ⋯⟩ ∈ (Multiset.filter (fun s => x ∉ s ∧ (SF.sets s ∨ SF.sets (s ∪ {x}))) (SF.ground.erase x).powerset.val).attach) ∧ a.erase x = val
      have : val ∪ {x} ⊆ SF.ground := by
        --obtain ⟨left, right⟩ := property
        exact SF.inc_ground (val ∪ {x}) pr
      let tmp := And.intro this pr
      use val ∪ {x}
      constructor
      ·
        simp_all only [Finset.mem_filter, Finset.mem_powerset]
        simp
        rw [Multiset.attach]
        simp
        constructor
        exact this
        constructor
        exact pr
        left
        exact property.2.2.1
      · let pr21 := property.2.1
        rw [Finset.union_comm]
        rw [←Finset.insert_eq x val]
        rw [Finset.erase_insert pr21]

  let bi:= @Finset.card_bij S T S.attach T.attach ii hi inj surj
  dsimp [S,T] at bi
  rw [Finset.card_attach] at bi
  rw [Finset.card_attach] at bi
  simp
  rw [bi]
  congr
  ext a
  apply Iff.intro
  · intro h
    simp_all only [Finset.mem_filter, Finset.mem_powerset]
    simp
  · intro h
    simp_all only [Finset.mem_filter, Finset.mem_powerset]
    simp

lemma trace_paralel_vertex_rare (SF: ClosureSystem α) [DecidablePred SF.sets] (x:α) (hx: x ∈ SF.ground):
  (p:(∃ y: α, x ≠ y ∧ parallel SF x y)) →
  ((∃ z:α, z ∈ SF.ground ∧ SF.toSetFamily.is_rare z) ↔ ∃ z:α, (z ∈ SF.ground \ {x}) ∧ (SF.toSetFamily.trace x hx (ground_card_ge_two SF x hx p)).is_rare z) :=
by
  intro p
  obtain ⟨y, hy, h⟩ := p
  --obtain ⟨left, right⟩ := h
  dsimp [SetFamily.is_rare]
  apply Iff.intro
  · intro hh
    obtain ⟨z, hz⟩ := hh
    obtain ⟨hz1, hz2⟩ := hz
    by_cases hzx: z = x
    case pos =>
      subst hzx
      simp_all only [Finset.mem_sdiff, Finset.mem_singleton]
      use y -- zがxのときは、代わりにyを使う。
      have :SF.degree z = SF.degree y := by
        exact parallel_same_degree SF z y h
      rw [this] at hz2
      constructor
      ·
        simp_all only [tsub_le_iff_right, zero_add, ne_eq]
        apply And.intro
        · dsimp [parallel] at h
          exact (h.2.2 SF.ground SF.has_ground).mp hx
        · apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [not_true_eq_false]
      ·
        simp_all only [tsub_le_iff_right, zero_add]
        let tpvd := trace_paralel_vertex_degree SF z hx y ⟨y, hy, h⟩ hy.symm
        let tpv := trace_paralel_vertex SF z hx ⟨y, hy, h⟩
        rw [←tpvd]
        rw [←tpv]
        exact hz2

    case neg =>
      obtain ⟨left, right⟩ := h
      use z
      constructor
      · simp_all only [Finset.mem_sdiff, Finset.mem_singleton]
        simp_all only [ne_eq, not_false_eq_true, tsub_le_iff_right, zero_add, and_self]
      · --ここで、
        --lemma trace_paralel_vertex_degree (SF: ClosureSystem α) [DecidablePred SF.sets] (x:α) (hx: x ∈ SF.ground) (z:α) (_:z ∈ SF.ground)
        --trace_paralel_vertex (SF: ClosureSystem α) [DecidablePred SF.sets] (x:α) (hx: x ∈ SF.ground)
        --を使う。
        let tpvd := trace_paralel_vertex_degree SF x hx z ⟨y, hy, ⟨left, right⟩⟩ hzx
        let tpv := trace_paralel_vertex SF x hx ⟨y, hy, ⟨left, right⟩⟩
        rw [←tpvd]
        rw [←tpv]
        exact hz2
  · obtain ⟨left, right⟩ := h
    intro h
    obtain ⟨z, hz⟩ := h
    obtain ⟨hz1, hz2⟩ := hz
    use z
    constructor
    · simp_all only [Finset.mem_sdiff, Finset.mem_singleton]
    · have : z ≠ x := by
        intro a
        subst a
        simp_all only [Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false, and_false]
      let tpvd := trace_paralel_vertex_degree SF x hx z ⟨y, hy, ⟨left, right⟩⟩ this
      let tpv := trace_paralel_vertex SF x hx ⟨y, hy, ⟨left, right⟩⟩
      rw [tpvd]
      rw [tpv]
      exact hz2

def is_Parallel (SF:ClosureSystem α)[DecidablePred SF.sets] (x y:α) : Prop :=
x ∈ SF.ground ∧ x ≠ y ∧ ∀ s : Finset α, SF.sets s → (x ∈ s ↔ y ∈ s)

--vはF.groundに含まれれるという条件が必要？
def isParallelFree (SF : ClosureSystem α) [DecidablePred SF.sets]: Prop :=
  ∀ (v₁ v₂ : α), v₁ ∈ SF.ground → v₂ ∈ SF.ground → v₁ ≠ v₂ → ¬ is_Parallel SF v₁ v₂

--n=0のときは、F.ground.card = 0なので、F.ground = ∅である。これは仮定により起こり得ない。
def P  {α :Type} [DecidableEq α][Fintype α] (n : Nat) : Prop :=
   (∀ (F : ClosureSystem α)[DecidablePred F.sets], F.ground.card = n → ∃ (v :α), v ∈ F.ground ∧ F.is_rare v)

def PP {α :Type} [DecidableEq α][Fintype α] (n : Nat) : Prop :=
   (∀ (F : ClosureSystem α)[DecidablePred F.sets], F.ground.card = n → isParallelFree F → ∃ (v :α), v ∈ F.ground ∧ F.is_rare v ∧ isParallelFree F)

theorem parallel_free_theorem  {α :Type} [Fintype α] [DecidableEq α] :
  (∀ (n:Nat), @P α _ _ n) ↔ (∀ (n:Nat), @PP α _ _ n) :=
by
  apply Iff.intro
  · dsimp [P, PP]
    intro h --簡単な方向。
    intro n
    intro F inst_1 a a_1
    subst a
    simp_all only [and_true]
  · intro h
    intro n
    apply @Nat.strong_induction_on  (λ n  => @P α _ _ n)
    intros n ih F dp fgc
    -- PP n を用いて P n を導く
    --let ipf := @isParallelFree α _ _ F dp
    by_cases h_parallel : @isParallelFree α _ _ F dp
    case pos =>
      -- F がパラレルを持たない場合、PP n を直接適用
      specialize h n F fgc h_parallel
      obtain ⟨v, hv_ground, hv_rare, _⟩ := h
      use v

    case neg =>
      -- F がパラレルを持つ場合、パラレルを削除して帰納仮定を適用
      -- ihにより小さいnでは、P nが成り立つことが入っている。
      dsimp [isParallelFree] at h_parallel
      push_neg at h_parallel
      obtain ⟨v₁, v₂, h_parallel_v⟩ := h_parallel
      obtain ⟨v1fg, v2fg, n12, right⟩ := h_parallel_v
      have h_subset : {v₁, v₂} ⊆ F.ground :=
      by
        subst fgc
        simp_all only [ne_eq]
        simp [Finset.insert_subset_iff]
        simp_all only [and_self]
      have h_card : ({v₁, v₂} : Finset α).card = 2 := by
        subst fgc
        simp_all only [ne_eq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
          Finset.card_singleton, Nat.reduceAdd]
      have gcard : F.ground.card >= 2:= by
        have : 2 ≤ F.ground.card := by
          rw [←h_card]
          exact Finset.card_le_card h_subset
        exact this

      let F' := F.trace v₁ v1fg gcard
      let F'_closure : ClosureSystem α := trace_closure_system F v₁ v1fg gcard
      have h_closure_ground:F'_closure.ground = F.ground \ {v₁} := by
        dsimp [F'_closure]
        dsimp [trace_closure_system]
        subst fgc
        simp_all only [ne_eq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
          Finset.card_singleton, Nat.reduceAdd]
        ext a : 1
        simp_all only [Finset.mem_erase, ne_eq, Finset.mem_sdiff, Finset.mem_singleton]
        apply Iff.intro
        · intro a_1
          simp_all only [not_false_eq_true, and_self]
        · intro a_1
          simp_all only [not_false_eq_true, and_self]

      have h_ground_card' : F'_closure.ground.card = n - 1 := by
        dsimp [F']
        dsimp [F'_closure]
        dsimp [trace_closure_system]
        subst fgc
        simp_all only [ne_eq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem,
          Finset.card_singleton, Nat.reduceAdd, Finset.card_erase_of_mem]

         --F'がrare vertexを持つことを示す。
      let tpv := trace_paralel_vertex_rare F v₁ v1fg ⟨v₂, n12, right⟩
      apply tpv.mpr
      have : n - 1 < n:= by
        subst fgc
        simp_all only [Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_not_mem, Finset.card_singleton,
          Nat.reduceAdd, tsub_lt_self_iff, Finset.card_pos, zero_lt_one, and_true, F']
        exact ⟨v₁, v1fg⟩
      let ihn := (ih (n-1)) this
      dsimp [P] at ihn
      let ihnf := ihn F'_closure  h_ground_card'
      rw [h_closure_ground] at ihnf
      exact ihnf
