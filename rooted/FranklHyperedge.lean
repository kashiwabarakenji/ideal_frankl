import LeanCopilot
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Finset.Union
import Mathlib.Tactic
import rooted.CommonDefinition
import rooted.RootedCircuits
import rooted.RootedImplication
import rooted.ClosureOperator
import rooted.RootedFrankl
import rooted.RootedSets
import rooted.Superior

variable {α : Type}  [DecidableEq α] [Fintype α]

open Classical

--n-1のサイズのhyperedgeがあるときは、U-xのxがrare。
theorem hyperedge_minusone  (SF: ClosureSystem α) [DecidablePred SF.sets] (x :SF.ground):
  SF.sets (SF.ground \ {x.val}) → SF.is_rare x:=
by
  intro SFS
  let M := SF.ground \ {x.val}
  have setM : SF.sets M :=
  by
    exact SFS
  let S := SF.ground.powerset.filter (fun s => SF.sets s ∧ x.val ∈ s)
  let T := SF.ground.powerset.filter (fun s => SF.sets s ∧ x.val ∉ s)
  let ii: S → T := fun s => ⟨s.val.erase x.val, by
    dsimp [T]
    rw [Finset.mem_filter]
    obtain ⟨sval, sproperty⟩ := s
    constructor
    ·

      simp_all only
      simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
      obtain ⟨left, right⟩ := sproperty
      intro x hx
      simp_all only [Finset.mem_erase, ne_eq]
      obtain ⟨left_2, right_1⟩ := hx
      exact left right_1
    · constructor
      ·
        simp_all only [T, S]
        obtain ⟨val, property⟩ := x
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
        obtain ⟨left, right⟩ := sproperty
        obtain ⟨left_1, right⟩ := right
        have :sval.erase val = M ∩ sval :=
        by
          simp_all only [S, M]
          ext a : 1
          simp_all only [Finset.mem_erase, ne_eq, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton,
            and_congr_left_iff, iff_and_self, S]
          intro a_1 a_2
          exact left a_1
        let sic := SF.intersection_closed sval M left_1 setM
        rw [this]
        rw [Finset.inter_comm]
        exact sic
      · apply Finset.not_mem_erase x.val
  ⟩
  have inj: ∀ s1 s2:S, ii s1 = ii s2 → s1 = s2 :=
  by
    dsimp [ii]
    intro s1 s2
    intro h
    ext y
    apply Iff.intro
    · intro hy
      by_cases hh:y = x
      case pos
        =>
        simp_all only [Subtype.mk.injEq, T, S]
        obtain ⟨val_2, property_2⟩ := s2
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset, S, T]
      case neg
        =>
        have : y ∈ s1.val.erase x :=
        by
          rw [@Finset.mem_erase]
          simp_all only [Subtype.mk.injEq, ne_eq, not_false_eq_true, and_self, T, S, ii]
        have : y ∈ s2.val.erase x :=
        by
          simp_all only [Subtype.mk.injEq, Finset.mem_erase, ne_eq, not_false_eq_true, true_and,and_self]
        simp_all only [Subtype.mk.injEq, Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
    · intro hy
      by_cases hh:y = x
      case pos
      =>
        simp_all only [Subtype.mk.injEq, T, S]
        obtain ⟨val_1, property_1⟩ := s1
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset, and_true, S]
      case neg
      =>
        have : y ∈ s1.val.erase x :=
        by
          simp_all only [Subtype.mk.injEq, Finset.mem_erase, ne_eq, not_false_eq_true, and_self, T, S, ii]
        --have : y ∈ s2.val.erase x :=
        --by
        --  simp_all only [Subtype.mk.injEq, Finset.mem_erase, ne_eq, not_false_eq_true, and_self, T, S, ii]
        rw [@Finset.mem_erase] at this
        exact this.2

  have :S.card <= T.card :=
  by
    let fcl := @Finset.card_le_card_of_injOn S T S.attach T.attach (fun s => ii s) (fun s hs => Finset.mem_attach _ _)
    have :Set.InjOn (fun s => ii s) ↑S.attach :=
    by
      simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp, S, T, ii]
      obtain ⟨val, property⟩ := x
      simp_all only
      intro s hs
      intro x₂ a a_1
      simp_all only [Finset.mem_coe, Finset.mem_attach, Subtype.mk.injEq]
      obtain ⟨val_1, property_1⟩ := s
      obtain ⟨val_2, property_2⟩ := x₂
      simp_all only [Subtype.mk.injEq]
      simp_all only [subset_refl, Finset.mem_filter, Finset.mem_powerset]
      obtain ⟨left, right⟩ := property_1
      obtain ⟨left_1, right_1⟩ := property_2
      obtain ⟨left_2, right⟩ := right
      obtain ⟨left_3, right_1⟩ := right_1
      apply inj
      · simp_all only [subset_refl]
      · simp_all only [subset_refl]
      · simp_all only [subset_refl]
      · simp_all only [subset_refl]
      · simp_all only [subset_refl]
      · simp_all only [subset_refl]
      · simp_all only [subset_refl]
    convert fcl this
    simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl,
      Finset.card_attach, S, T, ii]
    simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl,
      Finset.card_attach, S, T, ii]

  --convert (rare_and_card SF.toSetFamily x).mpr
  apply (rare_and_card SF.toSetFamily x).mpr
  dsimp [including_hyperedges]
  dsimp [deleting_hyperedges]
  dsimp [S,T] at this
  have Lin:Finset.filter (fun s => ↑x ∈ s ∧ SF.sets s) SF.ground.powerset = Finset.filter (fun s => SF.sets s ∧ ↑x ∈ s) SF.ground.powerset :=
  by
    simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl, S,
      T, ii]
    obtain ⟨val, property⟩ := x
    simp_all only [subset_refl]
    ext a : 1
    simp_all only [subset_refl, Finset.mem_filter, Finset.mem_powerset, and_congr_right_iff]
    intro a_1
    apply Iff.intro
    · intro a_2
      simp_all only [subset_refl, and_self]
    · intro a_2
      simp_all only [subset_refl, and_self]

  have Lnot:Finset.filter (fun s => ↑x ∉ s ∧ SF.sets s) SF.ground.powerset = Finset.filter (fun s => SF.sets s ∧ ↑x ∉ s) SF.ground.powerset :=
  by
    simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl, S, T,
      ii]
    obtain ⟨val, property⟩ := x
    simp_all only [subset_refl]
    ext a : 1
    simp_all only [subset_refl, Finset.mem_filter, Finset.mem_powerset, and_congr_right_iff]
    intro a_1
    apply Iff.intro
    · intro a_2
      simp_all only [subset_refl, not_false_eq_true, and_self]
    · intro a_2
      simp_all only [subset_refl, not_false_eq_true, and_self]
  /-これはうまくfilter_congrで書き換えれなかった。
  have equiv:∀ s :Finset α, SF.sets s ∧ ↑x ∉ s ↔  ↑x ∉ s ∧ SF.sets s :=
  by
    intro s
    simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl, S,
      T, ii]
    obtain ⟨val, property⟩ := x
    simp_all only [subset_refl]
    apply Iff.intro
    · intro a
      simp_all only [subset_refl, not_false_eq_true, and_self]
    · intro a
      simp_all only [subset_refl, not_false_eq_true, and_self]
  -/
  norm_cast at this
  norm_cast at Lin
  norm_cast at Lnot
  rw [Lin]
  rw [Lnot]

  linarith

--サイズn-1のhyperedgeと根付き集合の関係。既存の補題をあまり使わずに証明したので、ちょっと長い。
lemma hyperedge_minusone_rootedset (SF: ClosureSystem α) [DecidablePred SF.sets] (x :SF.ground):
  ¬ SF.sets (SF.ground.erase x.val) ↔ ValidPair.mk (SF.ground.erase x.val) x.val (show x.val ∉ (SF.ground.erase x.val) from
    by
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, Finset.coe_mem, and_true, not_false_eq_true]
    ) ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets :=
by
  apply Iff.intro
  · intro h
    dsimp [RootedSets.rootedsets]
    dsimp [rootedSetsFromSetFamily]
    dsimp [rootedSetsSF]
    dsimp [allCompatiblePairs]
    simp
    constructor
    ·
      obtain ⟨val, property⟩ := x
      simp_all only
      simp [allPairs]
      simp_all only [and_true]
      intro x hx
      simp_all only [Finset.mem_erase, ne_eq]
    · dsimp [isCompatible]
      constructor
      · simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, Finset.coe_mem, and_true, not_false_eq_true]
      · intro t ht sg
        by_cases hh:t = SF.ground
        case pos =>
          rw [hh]
          exact x.property
        case neg =>
          have inc: t ⊆ SF.ground :=
          by
            exact SF.inc_ground t ht
          have sinc : t ⊂ SF.ground :=
          by
            rw [Finset.ssubset_def]
            constructor
            exact inc
            by_contra h_contra
            have :t = SF.ground :=
            by
              exact Finset.Subset.antisymm inc h_contra
            contradiction
          have : x.val ∉ t:=
          by
            by_contra h_contra
            have : SF.ground ⊆ t:=
            by
              intro y
              by_cases x = y
              case pos =>
                rename_i h_1
                intro a
                subst h_1
                simp_all only [Finset.coe_mem]
              case neg =>
                intro a
                obtain ⟨val, property⟩ := x
                simp_all only
                apply sg
                simp_all only [Finset.mem_erase, ne_eq, and_true]
                apply Aesop.BuiltinRules.not_intro
                intro a_1
                subst a_1
                simp_all only [not_true_eq_false]
            have : SF.ground = t :=
            by
              exact Finset.Subset.antisymm this inc
            exact hh (id (Eq.symm this))
          have : t = SF.ground.erase x.val :=
          by
            obtain ⟨val, property⟩ := x
            simp_all only
            ext a : 1
            simp_all only [Finset.mem_erase, ne_eq]
            apply Iff.intro
            · intro a_1
              apply And.intro
              · apply Aesop.BuiltinRules.not_intro
                intro a_2
                subst a_2
                simp_all only
              · exact inc a_1
            · intro a_1
              obtain ⟨left, right⟩ := a_1
              apply sg
              simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, and_self]

          subst this
          simp_all only [not_true_eq_false]

  · intro h
    dsimp [rootedSetsFromSetFamily] at h
    dsimp [rootedSetsSF ] at h
    dsimp [allCompatiblePairs] at h
    dsimp [isCompatible] at h
    simp at h
    intro sfs
    let hh := h.2 (SF.ground.erase x.val) sfs
    simp at hh

--hyperedge_minusone_rootedsetを使いやすくしたもの。最初からこの形でよかった？
lemma hyperedge_minusone_rootedset' (SF : ClosureSystem α) [DecidablePred SF.sets] (x : SF.ground) :
  ¬ SF.sets (SF.ground.erase x.val) →
  ∃ vp : ValidPair α, vp.root = x.val ∧ vp.stem = SF.ground.erase x.val ∧ vp ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets :=
by
  intro sfs
  let vp := (hyperedge_minusone_rootedset SF x).mp sfs
  apply Exists.intro
  · apply And.intro
    on_goal 2 => apply And.intro
    on_goal 3 => {exact vp
    }
    · simp_all only
    · simp_all only



lemma hyperedge_minustwo_rootedset (SF: ClosureSystem α) [DecidablePred SF.sets] (x :SF.ground):
   (∀ s :Finset α, SF.sets s → s.card < SF.ground.card - 2) ↔
   (∀ x y:SF.ground , ∃ r:ValidPair α, r ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets ∧ x.val = r.root ∧  y.val ∉ r.stem ) :=
by
  apply Iff.intro
  · intro h
    --* 証明：サイズn-2のhyperedgeを持たないとする。n-1も持たないとする。
    --* 仮定より、任意の2点x,yを取った時に、U-x,yがhyperedgeでないことがわかる。
    intro x y
    have sfsx: ¬ SF.sets (SF.ground.erase x.val):=
      by
        by_contra h_contra
        have : (SF.ground.erase x.val).card = SF.ground.card -1 :=
        by
          simp_all only [ge_iff_le, tsub_le_iff_right, Finset.sdiff_subset, not_false_eq_true, forall_const,
            Finset.coe_mem, implies_true, imp_self, Finset.card_erase_of_mem]
        let htmp := h (SF.ground.erase x.val) h_contra
        norm_cast at htmp
        norm_cast at this
        rw [this] at htmp
        omega
    obtain ⟨r, hr1, hr2, hr3⟩ := hyperedge_minusone_rootedset' SF x sfsx

    by_cases x = y
    case pos =>
      use r
      rename_i h_1
      subst h_1
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, Finset.coe_mem, and_true, not_false_eq_true,
        and_self]

    case neg neqxy => --xとyが異なる場合

      have : (SF.ground \ {x.val,y.val}).card >= SF.ground.card - 2 :=
      by
        have hsub : (SF.ground \ {x.val, y.val}) = SF.ground \ insert x.val {y.val} :=
        by
          simp_all only [ge_iff_le, tsub_le_iff_right]
        have : ({x.val, y.val}:Finset α).card <= 2:=
        by
          exact Finset.card_insert_le _ _
        rw [hsub, Finset.card_sdiff]
        ·
          rename_i x_1
          simp_all only [ge_iff_le, tsub_le_iff_right]
          obtain ⟨val, property⟩ := x_1
          obtain ⟨val_1, property_1⟩ := x
          obtain ⟨val_2, property_2⟩ := y
          simp_all only
          omega
        · rw [@Finset.insert_subset_iff]
          simp_all only [Finset.coe_mem, Finset.singleton_subset_iff, and_self]

      have notset:¬(SF.sets (SF.ground \ ({x.val,y.val}:Finset α))) :=
      by
        by_contra h_contra
        specialize h (SF.ground \ {↑x, ↑y})
        let h := h h_contra
        linarith

      --lemma rootedset_setfamily (RS : RootedSets α) (SF:ClosureSystem α)
      --(eq:  rootedsetToClosureSystem RS = SF) :
      --∀ (s : Finset α), s ⊆ SF.ground → (¬ SF.sets s ↔ ∃ (p : ValidPair α), p ∈ RS.rootedsets ∧ p.stem ⊆ s ∧ p.root  ∈ (closureOperator SF (s.subtype (λ x => x ∈ SF.ground))).image Subtype.val ∧ p.root ∉ s) :=
      --let RS := rootedSetsFromSetFamily SF.toSetFamily
      --have eq: rootedsetToClosureSystem RS = SF :=
      --by
      --  exact closuresystem_rootedsets_eq SF
      let rsf := (rootedset_setfamily_cor SF (SF.ground \ ({x.val,y.val}:Finset α)))
      have :SF.ground \ {↑x, ↑y} ⊆ SF.ground :=
      by
        simp_all only [ge_iff_le, tsub_le_iff_right, Finset.sdiff_subset, Finset.mem_image, Subtype.exists,
          exists_and_right, exists_eq_right, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or, not_and,
          Decidable.not_not, rsf]
      specialize rsf this
      simp at rsf
      obtain ⟨p,hp1,hp2,hp3,hp4⟩ := rsf notset

      have root_xyg: p.root ∉ p.stem :=
      by
        exact p.root_not_in_stem

      --* このhyperedgeを排除する根付き集合が存在する。その根はxかyのどちらからである。
      --* ステムは、U-x,yに含まれるので、xを根としてyを含まないステムを持つか、yを根としてxを含まないステムを持つかのどちらかになる。
      have root_xy: p.root = x.val ∨ p.root = y.val :=
      by
        tauto

      cases root_xy
      case inl =>
        use p
        use hp1
        --* xを根に持ちyを含まない根付き集合が存在する時は証明完了。
        simp_all only [ge_iff_le, tsub_le_iff_right, Finset.sdiff_subset, not_false_eq_true, forall_const, Finset.coe_mem,
          not_true_eq_false, IsEmpty.forall_iff, imp_self]
        simp
        rw [@Finset.subset_sdiff] at hp2
        simp_all only [Finset.disjoint_insert_right, not_false_eq_true, Finset.disjoint_singleton_right, true_and]
      case inr =>
        --* yを根に持ちxを含まないと仮定。このとき、xを根としてyを含まないステムを持つことを証明。。


        --* xを根とする根付き集合は、n-1の大きさのhyperedgeも持たないとの仮定より、少なくとも一つは存在する。xが根でU-xがステムになる。

        rename_i hh
        --lemma closuresystem_rootedsets_implication (SF:ClosureSystem α)[DecidablePred SF.sets]:
        --let RS := rootedSetsFromSetFamily SF.toSetFamily
        --∀ p ∈ RS.rootedsets, ∀ q ∈ RS.rootedsets, q.root ∈ p.stem → p.root ∉ q.stem
        --→ ∃ r ∈ RS.rootedsets, r.root = p.root ∧ r.stem ⊆ p.stem ∪ q.stem \ {q.root}  :=
        let cri := closuresystem_rootedsets_implication SF r hr3 p hp1
        have : p.root ∈ r.stem :=
        by
          rw [hr2]
          rw [hh]
          simp_all only [ge_iff_le, tsub_le_iff_right, Finset.sdiff_subset, not_false_eq_true, forall_const,
            Finset.coe_mem, implies_true, imp_self, Finset.mem_erase, ne_eq, and_true]
          intro a
          simp_all only [not_true_eq_false]
          exact neqxy (Subtype.ext a.symm)
        let cri := cri this
        have :r.root ∉ p.stem :=
        by
          rw [hr1]
          rw [@Finset.subset_sdiff] at hp2
          simp_all only [ge_iff_le, tsub_le_iff_right, Finset.sdiff_subset, not_false_eq_true,
            forall_const, Finset.disjoint_insert_right, Finset.disjoint_singleton_right,
            Finset.coe_mem, implies_true]
        specialize cri this

        obtain ⟨rr,hrr1,hrr2,hrr3⟩ := cri

        use rr
        constructor
        · simp_all only [ge_iff_le, tsub_le_iff_right, Finset.sdiff_subset, not_false_eq_true, forall_const,
          Finset.coe_mem, implies_true, imp_self, Finset.mem_erase, ne_eq, and_true]
        · constructor
          · simp_all only [ge_iff_le, tsub_le_iff_right, Finset.sdiff_subset, not_false_eq_true, forall_const,
            Finset.coe_mem, implies_true, imp_self, Finset.mem_erase, ne_eq, and_true]
          · rw [hh] at hrr3
            by_contra h_contra
            --hrr3 : rr.stem ⊆ r.stem ∪ p.stem \ {↑y}























  /-

  * ステムの包含関係で最小なものが存在。根付きサーキット。そのようなものが存在するという補題rootedcircuits_minimality を利用。
  * xを根とする根付きサーキットは背理法の仮定より、ステムにyを必ず含むことになる。
  * この根付きサーキットと根にyを持つものと推論を考えると、xを根に持ち、yをステムに含まない根付きサーキットの存在がいえる。yを根に持つ根付きサーキットはxを含まないことに注意。推論の補題closuresystem_rootedsets_implicationを利用。こちら向きの証明完了。
  -/
  · intro h
    -- * 逆を示す。U-{x,y}を持つとすると、xを根にしてyを含まない根付きサーキットを考えると矛盾。
    sorry


--Ground - {x,y}というhyperedgeがあるとフランクルの予想の反例にならないということ。
--Ground - {x,y}がhyperedgeの時に{x,y}は優位でないということは、どちらかはrare vertex
lemma hyperedge_minustwo (SF: ClosureSystem α) [DecidablePred SF.sets] (x y :SF.ground) (neq: x ≠ y):
   SF.sets (SF.ground \ {x.val,y.val}) → ¬ superior SF {x.val,y.val}:=
by
  intro sfs
  let M:= SF.ground \ {x.val,y.val}
  have hM: SF.sets M :=
  by
    simp_all only [ne_eq, M]
  let S := SF.ground.powerset.filter (fun s => SF.sets s ∧ x.val ∈ s ∧ y.val ∈ s)
  let T := SF.ground.powerset.filter (fun s => SF.sets s ∧ x.val ∉ s ∧ y.val ∉ s)
  let ii: S → T := fun s => ⟨(s.val.erase x.val).erase y.val, by
    dsimp [T]
    rw [Finset.mem_filter]
    obtain ⟨sval, sproperty⟩ := s
    constructor
    ·
      simp_all [M, T]
      simp_all only [Finset.mem_filter, Finset.mem_powerset, S, M, T]
      obtain ⟨val, property⟩ := x
      obtain ⟨left, right⟩ := sproperty
      simp_all only [Subtype.mk.injEq]
      intro x hx
      simp_all only [Finset.mem_erase, ne_eq]
      obtain ⟨left_3, right_1⟩ := hx
      obtain ⟨left_4, right_1⟩ := right_1
      exact left right_1
    · constructor
      ·
        simp_all [M, S, T]
        simp_all only [Finset.mem_filter, Finset.mem_powerset, S, M, T]
        obtain ⟨val, property⟩ := x
        obtain ⟨val_1, property_1⟩ := y
        obtain ⟨left, right⟩ := sproperty
        obtain ⟨left_1, right⟩ := right
        obtain ⟨left_2, right⟩ := right
        simp_all only [Subtype.mk.injEq]
        have :(sval.erase val).erase val_1 = M ∩ sval :=
        by
          simp_all only [S, M]
          ext a : 1
          simp_all only [Finset.mem_erase, ne_eq, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton,
            and_congr_left_iff, iff_and_self, S]
          simp_all only [Finset.mem_insert, Finset.mem_singleton, not_or, M]
          apply Iff.intro
          · intro a_1
            simp_all only [not_false_eq_true, and_self, and_true, M]
            obtain ⟨left_3, right_1⟩ := a_1
            obtain ⟨left_4, right_1⟩ := right_1
            exact left right_1
          · intro a_1
            simp_all only [not_false_eq_true, and_self, M]
        let sic := SF.intersection_closed sval M left_1 hM
        rw [this]
        rw [Finset.inter_comm]
        exact sic
      · simp_all only [ne_eq, Finset.mem_erase, not_true_eq_false, false_and, and_false, not_false_eq_true, and_self,
        M, S, T]
  ⟩
  have inj: ∀ s1 s2:S, ii s1 = ii s2 → s1 = s2 :=
  by
    dsimp [ii]
    intro s1 s2
    intro h
    ext z
    apply Iff.intro
    · intro hz
      by_cases hh:z = x ∨ z = y
      case pos =>
        simp_all [ii, M, S, T]
        obtain ⟨xval, xproperty⟩ := x
        obtain ⟨yval, yproperty⟩ := y
        obtain ⟨s2val, s2property⟩ := s2
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
        cases hh with
        | inl h_1 =>
          subst h_1
          simp_all only
        | inr h_2 =>
          subst h_2
          simp_all only
      case neg =>
        simp_all [ii, M, S, T]
        obtain ⟨xval, xproperty⟩ := x
        obtain ⟨yval, yproperty⟩ := y
        obtain ⟨s1val, property_1⟩ := s1
        obtain ⟨s2val, property_2⟩ := s2
        simp at hh
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
        have : z ∈ s1val \ {xval,yval} :=
        by
          simp_all only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, or_self, not_false_eq_true,
            and_self, S]
        have : z ∈ s2val \ {xval,yval} :=
        by
          have :s1val \ {xval,yval} = (s1val.erase xval).erase yval :=
          by
            ext u
            apply Iff.intro
            · intro hu
              rw [Finset.mem_erase]
              rw [Finset.mem_erase]
              simp_all only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, or_self, not_false_eq_true,
                and_self, not_or, ne_eq, S]
            · intro hu
              rw [Finset.mem_erase] at hu
              rw [Finset.mem_erase] at hu
              simp_all only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, or_self, not_false_eq_true,
                and_self, ne_eq, S]

          simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and, Finset.mem_sdiff, Finset.mem_insert,
            Finset.mem_singleton, or_self, and_self, S]
        simp_all only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, or_self, not_false_eq_true, and_self,
          and_true, S]
    · intro hz
      by_cases hh:z = x ∨ z = y
      case pos =>
        simp_all [ii, M, S, T]
        obtain ⟨xval, xproperty⟩ := x
        obtain ⟨yval, yproperty⟩ := y
        obtain ⟨s1val, s1property⟩ := s1
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
        cases hh with
        | inl h_1 =>
          subst h_1
          simp_all only
        | inr h_2 =>
          subst h_2
          simp_all only
      case neg =>
        simp_all [ii, M, S, T]
        obtain ⟨xval, xproperty⟩ := x
        obtain ⟨yval, yproperty⟩ := y
        obtain ⟨s1val, property_1⟩ := s1
        obtain ⟨s2val, property_2⟩ := s2
        simp at hh
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
        have hz2: z ∈ s2val \ {xval,yval} :=
        by
          simp_all only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, or_self, not_false_eq_true,
            and_self, S]
        have : z ∈ s1val \ {xval,yval} :=
        by
          have :s2val \ {xval,yval} = (s2val.erase xval).erase yval :=
          by
            ext u
            apply Iff.intro
            · intro hu
              rw [Finset.mem_erase]
              rw [Finset.mem_erase]
              simp_all only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, or_self, not_false_eq_true,
                and_self, not_or, ne_eq, S]
            · intro hu
              rw [Finset.mem_erase] at hu
              rw [Finset.mem_erase] at hu
              simp_all only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, or_self, not_false_eq_true,
                and_self, ne_eq, S]

          --
          rw [this] at hz2
          rw [←h] at hz2
          rw [Finset.mem_erase] at hz2
          rw [Finset.mem_erase] at hz2
          simp_all only [not_false_eq_true, and_self, ne_eq, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
            or_self, S]

        simp_all only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, or_self, not_false_eq_true, and_self,
          and_true, S]

  have st_eq:S.card <= T.card :=
  by
    let fcl := @Finset.card_le_card_of_injOn S T S.attach T.attach (fun s => ii s) (fun s hs => Finset.mem_attach _ _)
    have :Set.InjOn (fun s => ii s) ↑S.attach :=
    by
      dsimp [Set.InjOn]
      intro x1 hx1 x2 hx2
      dsimp [ii]
      apply inj
    let fcl := fcl this
    convert fcl
    simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl,
      Finset.card_attach, ii, M, S, T]
    simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl,
      Finset.card_attach, ii, M, S, T]

  dsimp [superior]
  dsimp [S,T] at st_eq
  have : (Finset.filter (fun s => SF.sets s ∧ x.val ∈ s ∧ y.val ∈ s) SF.ground.powerset) = (Finset.filter (fun s => SF.sets s ∧ {x.val, y.val} ⊆ s) SF.ground.powerset) :=
  by
    ext z
    apply Iff.intro
    · intro h
      rw [Finset.mem_filter]
      constructor
      simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl, ii,
        M, S, T]
      constructor
      simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl, ii,
        M, S, T]
      rw [Finset.mem_filter] at h
      intro xx
      intro a
      simp_all [ii, M, S, T]
      obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := y
      cases a with
      | inl h =>
        subst h
        simp_all only [subset_refl, Finset.singleton_subset_iff, Finset.sdiff_subset]
      | inr h_1 =>
        subst h_1
        simp_all only [subset_refl, Finset.singleton_subset_iff, Finset.sdiff_subset]
    · intro h
      rw [Finset.mem_filter]
      rw [Finset.mem_filter] at h
      constructor
      · exact h.1
      · constructor
        · exact h.2.1
        · constructor
          · let h22 := h.2.2
            rw [@Finset.insert_subset_iff] at h22
            rw [@Finset.singleton_subset_iff] at h22
            simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl,
            Finset.singleton_subset_iff, Finset.coe_mem, ii, M, S, T]

          · let h22 := h.2.2
            rw [@Finset.insert_subset_iff] at h22
            rw [@Finset.singleton_subset_iff] at h22
            simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp, subset_refl,
            Finset.singleton_subset_iff, Finset.coe_mem, ii, M, S, T]

  rw [this] at st_eq

  have :(Finset.filter (fun s => SF.sets s ∧ ↑x ∉ s ∧ ↑y ∉ s) SF.ground.powerset) = (Finset.filter (fun s => SF.sets s ∧ {x.val, y.val} ∩ s = ∅) SF.ground.powerset) :=
  by
    ext z
    apply Iff.intro
    · intro h
      rw [Finset.mem_filter]
      rw [Finset.mem_filter] at h
      refine ⟨h.1,h.2.1,?_⟩
      simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp,
        Finset.singleton_subset_iff, Finset.coe_mem, subset_refl, not_false_eq_true, Finset.insert_inter_of_not_mem,
        Finset.singleton_inter_of_not_mem, Finset.empty_subset, ii, M, S, T]
    · intro h
      rw [Finset.mem_filter]
      rw [Finset.mem_filter] at h
      refine ⟨h.1,h.2.1,?_⟩
      let h22 := h.2.2
      simp at h22
      constructor
      · by_contra h_contra
        have : x.val ∈ {x.val, y.val} ∩ z :=
        by
          rw [@Finset.mem_inter]
          simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp,
            Finset.singleton_subset_iff, Finset.coe_mem, subset_refl, Finset.mem_insert, Finset.mem_singleton,
            true_or, and_self, ii, M, S, T]
        rw [← @Finset.not_nonempty_iff_eq_empty] at h22
        have :∃ u, u ∈ {↑x, ↑y} ∩ z :=
        by
           simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter, Finset.mem_powerset, and_imp,
             Finset.singleton_subset_iff, Finset.coe_mem, subset_refl, Finset.insert_inter_of_mem,
             Finset.empty_subset, Finset.insert_ne_empty, and_false, ii, M, S, T]
        exact h22 this
      · by_contra h_contra
        have : {↑x, ↑y} ∩ z ≠ ∅ :=
        by
          rw [← @Finset.nonempty_iff_ne_empty]
          use y.val
          rw [@Finset.mem_inter]
          simp_all [ii, M, S, T]
        contradiction

  rw [this] at st_eq

  linarith
