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
import rooted.GeneralLemma
import rooted.CommonDefinition
import rooted.ClosureOperator
import rooted.RootedSets
import rooted.RootedCircuits
import rooted.RootedImplication
import rooted.RootedFrankl
import rooted.Superior
import rooted.Bridge

variable {α : Type}  [DecidableEq α] [Fintype α]
set_option maxHeartbeats 300000 --増やさないとエラー

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
    · simp_all only
      simp_all only [Finset.mem_filter, Finset.mem_powerset,S]
      obtain ⟨left, right⟩ := sproperty
      intro x hx
      simp_all only [Finset.mem_erase, ne_eq]
      obtain ⟨left_2, right_1⟩ := hx
      exact left right_1

    · constructor
      ·
        simp_all only [S]
        obtain ⟨val, property⟩ := x
        simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
        obtain ⟨left, right⟩ := sproperty
        obtain ⟨left_1, right⟩ := right
        have :sval.erase val = M ∩ sval :=
        by
          simp_all only [S, M]
          ext a : 1
          simp_all only [Finset.mem_erase, ne_eq, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton,
            and_congr_left_iff, iff_and_self]
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
        simp_all only [Subtype.mk.injEq, S]
        obtain ⟨val_2, property_2⟩ := s2
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset, S]
      case neg
        =>
        have : y ∈ s1.val.erase x :=
        by
          rw [@Finset.mem_erase]
          simp_all only [Subtype.mk.injEq, ne_eq, not_false_eq_true, and_self, S]
        have : y ∈ s2.val.erase x :=
        by
          simp_all only [Subtype.mk.injEq, ne_eq, not_false_eq_true, true_and,and_self]
        simp_all only [Subtype.mk.injEq, Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
    · intro hy
      by_cases hh:y = x
      case pos
      =>
        simp_all only [Subtype.mk.injEq, S]
        obtain ⟨val_1, property_1⟩ := s1
        simp_all only
        simp_all only [Finset.mem_filter, Finset.mem_powerset, and_true, S]
      case neg
      =>
        have : y ∈ s1.val.erase x :=
        by
          simp_all only [Subtype.mk.injEq, Finset.mem_erase, ne_eq, not_false_eq_true, and_self, T, S, ii]
        rw [@Finset.mem_erase] at this
        exact this.2

  have :S.card <= T.card :=
  by
    let fcl := @Finset.card_le_card_of_injOn S T S.attach T.attach (fun s => ii s) (fun s hs => Finset.mem_attach _ _)
    have :Set.InjOn (fun s => ii s) ↑S.attach :=
    by
      simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter,  and_imp, S, ii]
      obtain ⟨val, property⟩ := x
      simp_all only
      intro s hs
      intro x₂ a a_1
      simp_all only [Finset.mem_coe, Finset.mem_attach, Subtype.mk.injEq]
      obtain ⟨val_1, property_1⟩ := s
      obtain ⟨val_2, property_2⟩ := x₂
      simp_all only [Subtype.mk.injEq]
      simp_all only [subset_refl, Finset.mem_filter, Finset.mem_powerset]
      apply inj
      · simp_all only [subset_refl]
      · simp_all only [subset_refl]
      · simp_all only [subset_refl]
      · simp_all only [subset_refl]
      · simp_all only [subset_refl]
      · simp_all only [subset_refl]
      · simp_all only [subset_refl]
    convert fcl this
    simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter,  and_imp, subset_refl,
      Finset.card_attach, S, T, ii]
    simp_all only [Subtype.mk.injEq, Subtype.forall, Finset.mem_filter,  and_imp, subset_refl,
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
            ext a : 1
            simp_all only [Finset.mem_erase, ne_eq]
            apply Iff.intro
            · intro a_1
              apply And.intro
              · intro a_2
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

--existsを使って、hyperedge_minusone_rootedsetを使いやすくしたもの。
lemma hyperedge_minusone_rootedset' (SF : ClosureSystem α) [DecidablePred SF.sets] (x : SF.ground) :
  ¬ SF.sets (SF.ground.erase x.val) ↔
  ∃ vp : ValidPair α, vp.root = x.val ∧ vp.stem = SF.ground.erase x.val ∧ vp ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets :=
by
  apply Iff.intro
  · intro sfs
    let vp := (hyperedge_minusone_rootedset SF x).mp sfs
    apply Exists.intro
    · apply And.intro
      on_goal 2 => apply And.intro
      on_goal 3 => {exact vp
      }
      · simp_all only
      · simp_all only
  · intro h
    obtain ⟨vp, hvp1, hvp2, hvp3⟩ := h
    let v := (hyperedge_minusone_rootedset SF x).mpr
    simp at v
    by_contra h_contra
    have : vp.stem ⊆ SF.ground.erase ↑x :=
    by
      simp_all only [subset_refl]
    let csl := ClosureSystemLemma SF (SF.ground.erase x.val) h_contra hvp3 this
    obtain ⟨val, property⟩ := x
    subst hvp1
    simp_all only
    simp [hvp2] at csl

--このファイルのメイン定理。n-1とn-2のhyperedgeがないときに、rooted setsはどうなるのか。
lemma hyperedge_minustwo_rootedset (SF: ClosureSystem α) [DecidablePred SF.sets] (hasempty:SF.has_empty):
   (∀ s :Finset α, SF.sets s → s.card < SF.ground.card - 2 ∨ s = SF.ground ) ↔
   (∀ x y:SF.ground , ∃ r:ValidPair α, r ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets ∧ x.val = r.root ∧  y.val ∉ r.stem ) :=
by
  apply Iff.intro
  · intro h
    --* 証明：サイズn-2のhyperedgeを持たないとする。n-1も持たないとする。
    --* 仮定より、任意の2点x,yを取った時に、U-x,yがhyperedgeでないことがわかる。
    intro x y
    have :SF.ground.erase x.val ≠ SF.ground:=
    by
      simp_all only [ne_eq, Finset.erase_eq_self, Finset.coe_mem, not_true_eq_false, not_false_eq_true]
    have sfsx: ¬ SF.sets (SF.ground.erase x.val):=
      by
        by_contra h_contra
        have : (SF.ground.erase x.val).card = SF.ground.card -1 :=
        by
          simp_all only [ Finset.sdiff_subset, not_false_eq_true,Finset.coe_mem,  Finset.card_erase_of_mem]
        let htmp := h (SF.ground.erase x.val) h_contra
        --norm_cast at htmp
        --norm_cast at this
        rw [this] at htmp
        simp at htmp
        omega
    have neqg:SF.ground \ {x.val,y.val} ≠ SF.ground:=
    by
      simp_all only [ne_eq, Finset.coe_mem, not_true_eq_false, not_false_eq_true, sdiff_eq_left,
        Finset.disjoint_insert_right, Finset.disjoint_singleton_right, and_self]--
    obtain ⟨r, hr1, hr2, hr3⟩ := (hyperedge_minusone_rootedset' SF x).mp sfsx

    by_cases x = y
    case pos =>
      use r
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, Finset.coe_mem, and_true, not_false_eq_true]

    case neg neqxy => --xとyが異なる場合

      have : (SF.ground \ {x.val,y.val}).card >= SF.ground.card - 2 :=
      by
        have hsub : (SF.ground \ {x.val, y.val}) = SF.ground \ insert x.val {y.val} :=
        by
          simp_all only [ge_iff_le]
        have : ({x.val, y.val}:Finset α).card <= 2:=
        by
          exact Finset.card_insert_le _ _
        rw [hsub, Finset.card_sdiff]

        ·
          simp_all only
          omega
        · rw [@Finset.insert_subset_iff]
          simp_all only [Finset.coe_mem, Finset.singleton_subset_iff, and_self]

      have notset:¬(SF.sets (SF.ground \ ({x.val,y.val}:Finset α))) :=
      by
        by_contra h_contra
        specialize h (SF.ground \ {↑x, ↑y})
        let h := h h_contra
        simp at h
        linarith

      let rsf := (rootedset_setfamily_cor SF (SF.ground \ ({x.val,y.val}:Finset α)))
      have :SF.ground \ {↑x, ↑y} ⊆ SF.ground :=
      by
        simp_all only [ Finset.sdiff_subset, Finset.mem_image,exists_eq_right, Finset.mem_sdiff, Finset.mem_insert,  not_and]
      specialize rsf this
      simp at rsf
      obtain ⟨p,hp1,hp2,hp3,hp4⟩ := rsf.mp notset
      clear notset

      --わざわざ補題にすることもなさそう。
      --have root_xyg: p.root ∉ p.stem :=
      --by
      --  exact p.root_not_in_stem

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
        simp_all only [ not_false_eq_true, Finset.coe_mem, not_true_eq_false,  imp_self]
        simp
        rw [@Finset.subset_sdiff] at hp2
        simp_all only [Finset.disjoint_insert_right, not_false_eq_true, Finset.disjoint_singleton_right, true_and]
      case inr =>
        --* yを根に持ちxを含まないと仮定。このとき、xを根としてyを含まないステムを持つことを証明。
        --* xを根とする根付き集合は、n-1の大きさのhyperedgeも持たないとの仮定より、少なくとも一つは存在する。xが根でU-xがステムになる。

        rename_i hh
        let cri := closuresystem_rootedsets_implication SF r hr3 p hp1
        have : p.root ∈ r.stem :=
        by
          rw [hr2]
          rw [hh]
          simp_all only [ge_iff_le,  Finset.sdiff_subset, Finset.coe_mem, Finset.mem_erase, ne_eq, and_true]
          intro a
          exact neqxy (Subtype.ext a.symm)
        let cri := cri this
        have :r.root ∉ p.stem :=
        by
          rw [hr1]
          rw [@Finset.subset_sdiff] at hp2
          simp_all only [not_false_eq_true,Finset.disjoint_insert_right, Finset.coe_mem]
        specialize cri this

        --根付き集合と根にyを持つものと推論を考えると、xを根に持ち、yをステムに含まない根付き集合の存在がいえる。yを根に持つ根付きサーキットはxを含まないことに注意。推論の補題closuresystem_rootedsets_implicationを利用。こちら向きの証明完了。
        obtain ⟨rr,hrr1,hrr2,hrr3⟩ := cri

        use rr
        constructor
        · simp_all only [ge_iff_le, tsub_le_iff_right, Finset.sdiff_subset, not_false_eq_true, forall_const,
          Finset.coe_mem, implies_true, imp_self, Finset.mem_erase, ne_eq, and_true]
        · constructor
          · simp_all only [Finset.sdiff_subset, not_false_eq_true,Finset.coe_mem, Finset.mem_erase, ne_eq]
          · rw [hh] at hrr3
            by_contra h_contra
            --hrr3 : rr.stem ⊆ r.stem ∪ p.stem \ {↑y}
            rw [@Finset.subset_sdiff] at hrr3
            simp_all only [Finset.sdiff_subset, Finset.coe_mem, implies_true, Finset.disjoint_singleton_right]

  · intro h
    -- * 逆を示す。U-{x,y}を持つとすると、xを根にしてyを含まない根付きサーキットを考えると矛盾。台集合が1点のときを分離した方がいいか。
    by_cases hc:SF.ground.card = 1
    case pos =>  --台集合が1点のときは、特殊なので別扱い。証明が無駄に長くなった。
      --台集合の大きさが1だと、根付き集合のステムが空集合になる。すると、空集合がhyperedgeでなくなるので、仮定に矛盾する。
      obtain ⟨x,hx⟩ := Finset.card_eq_one.1 hc
      have xg: x ∈ SF.ground:=
      by
        simp_all only [Subtype.forall, Finset.mem_singleton, forall_eq, Finset.card_singleton]
      let hxx := h ⟨x,xg⟩ ⟨x,xg⟩
      obtain ⟨r,hr⟩ := hxx
      have : r.stem = ∅:=
      by
        by_contra h_contra
        rw [← @Finset.not_nonempty_iff_eq_empty] at h_contra
        rw [not_not] at h_contra
        obtain ⟨y,hy⟩ := h_contra
        have : x ≠ y:=
        by
          simp_all only [Subtype.forall, Finset.mem_singleton, forall_eq, Finset.card_singleton]
          simp_all only [Finset.mem_singleton]
          obtain ⟨left, right⟩ := hr
          obtain ⟨left_2, right⟩ := right
          subst left_2
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [not_true_eq_false]
        have : y ∈ SF.ground:=
        by
          let rsf := ((rootedSetsFromSetFamily SF.toSetFamily).inc_ground r hr.1).1
          have :(rootedSetsFromSetFamily SF.toSetFamily).ground = SF.ground:=
          by
            simp_all only [ Finset.mem_singleton, forall_eq, Finset.card_singleton, ne_eq]
            exact hx
          rw [this] at rsf
          rw [hx]
          simp_all only [Subtype.forall, forall_eq, ne_eq,Finset.subset_singleton_iff]
          simp_all only [Finset.mem_singleton]
          cases rsf with
          | inl h => simp_all only [Finset.not_mem_empty]
          | inr h_1 => simp_all only [Finset.mem_singleton, not_true_eq_false]
        simp_all only [Finset.mem_singleton, forall_eq, Finset.card_singleton, ne_eq, not_true_eq_false]

      --ステムが空だと空集合がhyperedgeでなくなる。空集合がhyperedgeであるという仮定に反する。
      let het := (has_empty_theorem3 SF).mpr
      have :(∃(x : { x // x ∈ SF.ground }), ∃ r ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets, r.root = ↑x ∧ r.stem = ∅) :=
      by
        use ⟨x,xg⟩
        use r
        use hr.1
        constructor
        simp_all only [Subtype.forall, Finset.mem_singleton,Finset.card_singleton, Finset.not_mem_empty,not_false_eq_true]
        exact this
      specialize het this
      contradiction

    case neg =>
      by_contra h_contra
      push_neg at h_contra
      obtain ⟨s, hs1, hs2⟩ := h_contra
      have sinc: s ⊆ SF.ground :=
      by
        exact SF.inc_ground s hs1
      have geq1: SF.ground.card ≥ 1:=
      by
        simp_all only [Subtype.forall, tsub_le_iff_right, Finset.one_le_card]
        obtain ⟨left, right⟩ := hs2
        contrapose! right
        simp_all only [Finset.not_nonempty_iff_eq_empty, Finset.subset_empty,  zero_add, zero_le]
      by_cases cdg : s = SF.ground
      case pos =>
        exact hs2.2 cdg
      case neg =>

      by_cases cd: s.card = SF.ground.card - 1
      case pos =>
        have hdiff : SF.ground.card - s.card = 1 :=
        by
          norm_cast at cd
          rw [cd]
          rw [Nat.sub_sub_self geq1]

        have :∃ x :SF.ground, s = SF.ground \ {x.val} :=
        by
          have hdiff_set : (SF.ground \ s).card = 1 :=
          by
            simp_all only [Subtype.forall,ne_eq, ge_iff_le, Finset.one_le_card]
            obtain ⟨left, right⟩ := hs2
            rw [Finset.card_sdiff]
            · simp_all only
            · simp_all only
          obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hdiff_set
          have : x ∈ SF.ground :=
          by
            rw [@Finset.Subset.antisymm_iff] at hx
            simp_all only [Subtype.forall, Finset.sdiff_eq_empty_iff_subset, Finset.singleton_subset_iff,Finset.mem_sdiff]
          use ⟨x,this⟩
          simp
          exact Eq.symm (sdiff_eq_symm sinc hx)
        obtain ⟨x,hx⟩ := this
        let hmr := (hyperedge_minusone_rootedset' SF x).mpr

        have :(∃ vp, vp.root = ↑x ∧ vp.stem = SF.ground.erase ↑x ∧ vp ∈ (rootedSetsFromSetFamily SF.toSetFamily).rootedsets):=
        by
          have:(SF.ground.erase x.val).Nonempty :=
          by
            --(SF.ground.erase x.val).Nonemptyは、hc : ¬SF.ground.card = 1とSF.ground.Nonemptyより。自明なのに証明が長い。
            have : SF.ground.card ≥ 2:=
            by
              subst hx
              simp_all only [Subtype.forall, Finset.one_le_card, Finset.coe_mem,not_false_eq_true, Finset.sdiff_subset]
              obtain ⟨val, property⟩ := x
              simp_all only
              omega
            have h_card : (SF.ground.erase x.val).card = SF.ground.card - 1 :=  Finset.card_erase_of_mem x.property
            have h_pos : (SF.ground.card - 1) ≥ 1 := by omega
            have :(SF.ground.erase x.val).card ≥ 1:=
            by
              subst hx
              simp_all only [Finset.one_le_card, Finset.coe_mem, sdiff_eq_left, Finset.disjoint_singleton_right]
            apply Finset.card_pos.mp
            rename_i this_1
            simp_all only [ Finset.coe_mem, Finset.sdiff_subset,Finset.one_le_card,tsub_pos_iff_lt]
            exact this_1
          obtain ⟨y, hy⟩ := this
          have : y ∈ SF.ground :=
          by
            subst hx
            simp_all only [ Finset.one_le_card, Finset.mem_erase, sdiff_eq_left, Finset.disjoint_singleton_right, Finset.sdiff_subset]
          let hh := h x ⟨y, this⟩
          obtain ⟨vp, hvp1, hvp2,hvp3⟩ := hh
          let vp' := ValidPair.mk (SF.ground.erase x.val) x.val (show x.val ∉ (SF.ground.erase x.val) from
            by
              simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, Finset.coe_mem, and_true, not_false_eq_true]
              subst hx
              simp_all only [Subtype.forall, Finset.sdiff_subset,false_and, not_false_eq_true]
          )
          let siu := stem_is_upward_closed SF vp vp' hvp1
          have :vp.root = vp'.root :=
          by
            subst hx
            simp_all only [ not_false_eq_true, vp']
          specialize siu this
          have : vp.stem ⊆ vp'.stem :=
          by
            have :vp'.stem = SF.ground.erase x :=
            by
              dsimp [vp']
            rw [this]
            intro z
            intro hz
            by_cases hz1: z = x
            case pos =>
              subst hz1
              simp_all only [Finset.mem_erase, ne_eq, Finset.mem_singleton, Finset.coe_mem]
              simp
              --hvp2 : ↑x = vp.root
              rename_i th
              rw [←th] at hz
              exact vp.root_not_in_stem hz
            case neg =>
              by_cases hz2: z = y
              case pos =>
                subst hz2
                simp_all only [Finset.mem_erase,  Finset.mem_singleton, Finset.coe_mem]
              case neg =>
                rw [Finset.mem_erase]
                constructor
                · exact hz1
                · let rsf := ((rootedSetsFromSetFamily SF.toSetFamily).inc_ground vp hvp1).1
                  have : (rootedSetsFromSetFamily SF.toSetFamily).ground = SF.ground:=
                  by
                    dsimp [rootedSetsFromSetFamily]
                  rw [this] at rsf
                  exact rsf hz

          specialize siu this
          have : vp'.stem ⊆ SF.ground :=
          by
            dsimp [vp']
            exact Finset.erase_subset (↑x) SF.ground
          specialize siu this
          use vp'
          constructor
          · dsimp [vp']
          · constructor
            · dsimp [vp']
            · exact siu
        rw [hx] at hs1
        rw [←Finset.erase_eq] at hs1
        exact (hmr this) hs1

      --仮定hから、xをrootで、U-x内にステムがあるものが存在するので、補題より矛盾。
      case neg =>--cd: s.card = SF.ground.card - 1の否定
        have : s.card = SF.ground.card - 2:=
        by
          have s_le: s.card ≤ SF.ground.card :=
          by
            apply Finset.card_le_card
            exact sinc
          have neqs: s.card ≠ SF.ground.card :=
          by
            by_contra h_contra
            have :SF.ground.card ≤ s.card :=
            by
              linarith

            let fe := Finset.eq_of_subset_of_card_le sinc this
            simp_all only [ le_add_iff_nonneg_right, not_true_eq_false, and_false, fe]
          simp_all only [ne_eq, not_false_eq_true, and_true,Finset.one_le_card]
          omega
        have geq2: SF.ground.card ≥ 2:=
        by
          simp_all only [Subtype.forall, not_false_eq_true, Finset.one_le_card]
          omega

        let ete := exists_two_elements_removed sinc this geq2
        obtain ⟨x, y, hxy⟩ := ete

        let hh := h ⟨x, hxy.1⟩ ⟨y, hxy.2.1⟩
        obtain ⟨r, hr1, hr2, hr3⟩ := hh

        let r' := ValidPair.mk s x (show x ∉ s from
          by
            simp_all only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or, not_and, ne_eq]
            subst hr2
            simp_all only [Subtype.forall, not_false_eq_true, and_self, ge_iff_le, Finset.one_le_card]
            obtain ⟨left, right⟩ := hxy
            obtain ⟨left_1, right⟩ := right
            subst right
            simp_all only [ sdiff_eq_left, Finset.disjoint_insert_right,
              Finset.disjoint_singleton_right, and_self, not_false_eq_true, Finset.mem_sdiff, Finset.mem_insert,
              true_or, and_false]--
        )

        let siu := stem_is_upward_closed SF r r' hr1
        have : r.root = r'.root:=
        by
          simp_all only [Subtype.forall, not_false_eq_true, Finset.one_le_card,r']
          obtain ⟨left, right⟩ := hxy
          obtain ⟨left_1, right⟩ := right
          subst right
          rw [← hr2]
        specialize siu this
        have : r.stem ⊆ SF.ground \ {x, y} :=
        by
          --hr3
          intro z
          intro hz
          rw [Finset.mem_sdiff]
          constructor
          · have: r.stem ⊆ SF.ground :=
            by
              exact ((rootedSetsFromSetFamily SF.toSetFamily).inc_ground r hr1).1
            exact this hz
          · simp at hr3
            by_contra h_contra
            simp at h_contra
            cases h_contra
            case inl hh =>
              let nrs := r.root_not_in_stem
              subst hh this
              simp_all only [Subtype.forall, le_refl, ne_eq, not_false_eq_true, and_self, ge_iff_le,
                Finset.one_le_card, nrs]
            case inr hh =>
              subst hh this
              simp_all only [Subtype.forall, le_refl, ne_eq, not_false_eq_true, and_self, ge_iff_le,
                Finset.one_le_card]
        have : r.stem ⊆ r'.stem :=
        by
          rename_i this_2
          subst this_2
          simp_all only [Subtype.forall, le_refl, ne_eq, not_false_eq_true, and_self, ge_iff_le, Finset.one_le_card,
            forall_const, r']
        specialize siu this
        have :r'.stem ⊆ SF.ground :=
        by
          simp_all only [Subtype.forall, not_false_eq_true, Finset.one_le_card, r']
        specialize siu this
        --r'の存在と、sがhyperedgeであることに矛盾。
        let RS := (rootedSetsFromSetFamily SF.toSetFamily)
        have exis: ∃ (p : ValidPair α), p ∈ RS.rootedsets ∧ p.stem ⊆ s ∧ p.root  ∈ SF.ground ∧ p.root ∉ s :=
        by
          use r'
          constructor
          ·
            obtain ⟨left, right⟩ := hxy
            obtain ⟨left_1, right⟩ := right
            subst right
            exact siu
          · constructor
            · rw [←hxy.2.2]
              let hh:= h ⟨x,hxy.1⟩ ⟨y,hxy.2.1⟩
              obtain ⟨r, hr1, hr2, hr3⟩ := hh
              intro z
              by_cases hz: z = x
              case pos =>
                intro a
                subst hz hr2
                simp_all only [Subtype.forall, le_refl, Finset.one_le_card, r']
              case neg =>
                by_cases hz2: z = y
                case pos =>
                  intro hz3
                  rw [Finset.mem_sdiff]
                  constructor
                  · subst hr2 hz2
                    simp_all only [Subtype.forall, le_refl, ne_eq, not_false_eq_true, and_self, ge_iff_le,
                      Finset.one_le_card, r']
                  ·
                    subst hr2 hz2
                    simp_all [r']
                    obtain ⟨left, right⟩ := hxy
                    obtain ⟨left_1, right⟩ := right
                    subst right
                    simp_all only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, or_true,not_true_eq_false]--

                case neg =>
                  intro hz3
                  rw [Finset.mem_sdiff]
                  constructor
                  ·
                    subst hr2
                    simp_all only [r']
                    obtain ⟨left, right⟩ := hxy
                    obtain ⟨left_1, right⟩ := right
                    subst right
                    simp_all only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_false_eq_true]
                  ·
                    subst hr2
                    simp_all only [Subtype.forall,  not_false_eq_true,Finset.one_le_card, Finset.mem_insert, Finset.mem_singleton, or_self, r']

            · constructor
              · rename_i this_2 this_3 this_4
                subst this_2
                simp_all only [Subtype.forall,  not_false_eq_true, and_self, Finset.one_le_card, r']

              · rename_i this_2 this_3 this_4
                subst this_2
                simp_all only [r']
                obtain ⟨left, right⟩ := hxy
                obtain ⟨left_1, right⟩ := right
                subst right
                simp_all only [Finset.mem_sdiff, Finset.mem_insert, true_or, not_true_eq_false,and_false, not_false_eq_true]--

        have sinc: s ⊆ SF.ground :=
        by
          rename_i this_2 this_3 this_4
          subst this_2
          simp_all only [Subtype.forall,  not_false_eq_true, and_self,Finset.one_le_card, r']

        let rs2 := (rootedset_setfamily_cor SF s sinc).mpr exis
        exact rs2 hs1

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
