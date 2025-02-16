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
import Mathlib.Tactic
import LeanCopilot

-- 有限集合の型
variable {α : Type} [Fintype α] [DecidableEq α]

open Classical  --これでsetsのdecidablePredの問題が解決した。

-- ValidPair の定義: ステム stem と根 root。Validは、根がステムに含まれていないことを示す。
--個々の根つき集合は、ValidPairになる。根つき集合の族は、RootedSetsなどで表す。
@[ext]
structure ValidPair (α : Type) where
  stem : Finset α
  root : α
  root_not_in_stem : root ∉ stem

--Valid性を満たすとは限らないステムと根の組。allVaildPairsの定義に使う。
noncomputable def allPairs (SF : SetFamily α) : Finset (Finset α × α) :=
  SF.ground.powerset.product SF.ground

--compatibleは、集合族で排除されない根つき集合を表す。
def isCompatible (SF : SetFamily α) (stem : Finset α) (root : α) : Prop :=
  root ∉ stem ∧ ∀ t, SF.sets t → (stem ⊆ t → root ∈ t)

--disjointの証明付きの構造。集合族から定義される根付き集合。
noncomputable def allCompatiblePairs (SF : SetFamily α) : Finset (Finset α × α) :=
  (allPairs SF).filter (λ (p : Finset α × α) =>
    isCompatible SF p.1 p.2
  )

--集合族から定義される根付き集合全体を与える関数。
noncomputable def rootedSetsSF (SF : SetFamily α) [DecidableEq α] : Finset (ValidPair α) :=
  (allCompatiblePairs SF).attach.image (λ ⟨p, h_p_in⟩ =>
    -- p : (Finset α × α)   -- h_p_in : p ∈ allCompatiblePairs SF
    ValidPair.mk p.1 p.2 (by
      -- root_not_in_stem の証明
      simp only [allCompatiblePairs, allPairs, Finset.mem_filter] at h_p_in
      exact h_p_in.2.1
    )
  )

--根付き集合族の構造。台集合つき。rootやstemはsubtypeではない。
@[ext]
structure RootedSets (α : Type) [DecidableEq α] where
  ground : Finset α
  rootedsets : Finset (ValidPair α)
  inc_ground : ∀ p ∈ rootedsets, p.stem ⊆ ground ∧ p.root ∈ ground
  nonempty_ground : ground.Nonempty

--subtypeのvalidpiarに変換する関数。
noncomputable def rootedpair_to_subtype (RS : RootedSets α) (p: ValidPair α) (pr: p ∈ RS.rootedsets): ValidPair { x // x ∈ RS.ground } :=
  ValidPair.mk (p.stem.subtype (λ x => x ∈ RS.ground)) ⟨p.root, (RS.inc_ground p pr).2⟩
  (by
    simp_all only [Finset.mem_subtype]
    exact p.root_not_in_stem
  )

--subtypeに関する補題。どこかにまとめた方が良い。
lemma subtype_val_eq {α : Type} {p : α → Prop} (x y : Subtype p) :
    x = y ↔ Subtype.val x = Subtype.val y := by
  apply Iff.intro
  · intro h; rw [h]
  · intro h; ext; exact h

-- RootedSetsにフィルタされた通常の集合族の定義。こちらはSetFamilyではなく、ただの集合族。
noncomputable def filteredFamily (RS : RootedSets α):
  Finset (Finset α):=
RS.ground.powerset.filter (λ B =>
    ∀ (p : ValidPair α), p ∈ RS.rootedsets → ¬(p.stem ⊆ B ∧ p.root ∉ B))

--RootedSetsにフィルタされたSetFamilyを与える定義。
noncomputable def filteredSetFamily (RS : RootedSets α):
  SetFamily α :=
{
  ground := RS.ground

  sets := fun s => s ∈ filteredFamily RS

  inc_ground :=
  by
    intro s a
    rw [filteredFamily] at a
    simp_all only [Finset.mem_filter, Finset.mem_powerset]--

  nonempty_ground := by
    obtain ⟨x, hx⟩ := RS
    simp_all only
}

--filteredFamilyが共通部分について閉じていること。次の言明の補題になる。
omit [Fintype α] in
theorem filteredFamily_closed_under_intersection (RS : RootedSets α) [DecidablePred (λ p => p ∈ RS.rootedsets)]:
  ∀ B₁ B₂ : Finset α, B₁ ∈ filteredFamily RS → B₂ ∈ filteredFamily RS → (B₁ ∩ B₂) ∈ filteredFamily RS :=
by
  intros B₁ B₂ hB₁ hB₂
  simp only [filteredFamily, Finset.mem_filter] at hB₁ hB₂ ⊢
  obtain ⟨hB₁sub, hB₁cond⟩ := hB₁
  obtain ⟨hB₂sub, hB₂cond⟩ := hB₂
  have hInterSub : B₁ ∩ B₂ ⊆ RS.ground :=
  by
    simp_all only [Finset.mem_powerset, not_and, Decidable.not_not]
    intro p hp
    simp_all only [Finset.mem_inter]
    obtain ⟨left, right⟩ := hp
    exact hB₂sub right
  constructor
  simp_all only [Finset.mem_powerset, not_and, Decidable.not_not]

  intro p hp
  specialize hB₁cond p hp
  specialize hB₂cond p hp
  by_contra hContr
  simp only [Finset.subset_inter_iff, not_and, not_not] at hContr
  simp_all only [true_and, Decidable.not_not, Finset.mem_inter,  not_true_eq_false]--

--RootedSetsが与えられた時に、閉集合族を与える関数
def rootedsetToClosureSystem (RS : RootedSets α) :
  ClosureSystem α :=
{
  ground := RS.ground

  intersection_closed := filteredFamily_closed_under_intersection RS,

  has_ground := by
    simp only [filteredFamily, Finset.mem_filter]
    constructor
    simp only [Finset.mem_powerset, not_and, Decidable.not_not]
    intro p hp
    simp_all only

    intro q hq
    have : q.root ∈ RS.ground := by
      exact (RS.inc_ground q hq).2
    simp_all only [not_true_eq_false, and_false, not_false_eq_true]

  inc_ground := by
    intro p hp
    simp only [filteredFamily, Finset.mem_filter] at hp
    obtain ⟨hsub, hcond⟩ := hp
    simp_all only [Finset.mem_powerset, not_and, Decidable.not_not]

  nonempty_ground := RS.nonempty_ground
}

-- SetFamily から RootedSets を構築する関数 noncomputableはつけないとエラー。
noncomputable def rootedSetsFromSetFamily (SF : SetFamily α) [DecidableEq α] [DecidablePred SF.sets][Fintype SF.ground] : RootedSets α :=
  {
    ground := SF.ground

    rootedsets := rootedSetsSF SF

    inc_ground := by
      intro p pa
      dsimp [rootedSetsSF] at pa
      dsimp [allCompatiblePairs] at pa
      simp_all --必要
      obtain ⟨w, h⟩ := pa
      obtain ⟨w_1, h⟩ := h
      obtain ⟨h2, h⟩ := h
      obtain ⟨left, right⟩ := h2
      subst h
      dsimp [allPairs] at left
      --rw [Finset.product] at left
      set wp :=  (w, w_1)
      let fmp := @Finset.mem_product _ _ SF.ground.powerset SF.ground wp --なぜか直接rwできなかった。
      have :wp.1 ∈ SF.ground.powerset ∧ wp.2 ∈ SF.ground  :=
      by
        exact fmp.mp left
      rw [Finset.mem_powerset] at this
      dsimp [wp] at this
      exact this

    nonempty_ground := SF.nonempty_ground
  }

--根付き集合表現と両立する集合sを取り出すと、本当に両立しているという証明。ステムを含むと根を含むの、生成表現からスタートしている版。
lemma rootedpair_compatible (RS : RootedSets α):
  ∀ s:Finset α, (rootedsetToClosureSystem RS).sets s → (∀ r ∈ RS.rootedsets, r.stem ⊆ s → r.root ∈ s) :=
by
  intro s hs
  intro r hr
  intro rs
  dsimp [rootedsetToClosureSystem] at hs
  dsimp [filteredFamily] at hs
  simp_all only [not_and, Decidable.not_not, Finset.mem_filter, Finset.mem_powerset]

--sがhyperedgeであるときには、sにステムが含まれて、sの外にrootがあるような根付き集合はない。
--rootedpair_compatibleと似ているがこちらは、閉包システムからスタートしている。
lemma ClosureSystemLemma  (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  ∀ s : Finset α, SF.sets s → rc ∈(rootedSetsFromSetFamily SF.toSetFamily).rootedsets
  → rc.stem ⊆ s → rc.root ∈ s :=
by
  intro s a a_1 a_2
  dsimp [rootedSetsFromSetFamily] at a_1
  dsimp [rootedSetsSF] at a_1
  dsimp [allCompatiblePairs] at a_1
  rw [Finset.mem_image] at a_1
  obtain ⟨w, h⟩ := a_1
  obtain ⟨val, property⟩ := w
  obtain ⟨fst, snd⟩ := val
  obtain ⟨left, right⟩ := h
  subst right
  simp_all only
  dsimp [isCompatible] at property
  dsimp [allPairs] at property
  have pro1:snd ∉ fst := by
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    simp [a_1, a_2] at property
  have pro2 :∀ (t : Finset α), SF.sets t → fst ⊆ SF.ground → fst ⊆ t  → snd ∈ t :=
  by
    intro t _ _ _
    --dsimp [Finset.product] at property
    simp at property
    simp_all only [not_false_eq_true]

  have pro3: fst ⊆ SF.ground :=
  by
    have: s ⊆ SF.ground := by
      exact SF.inc_ground s a
    tauto

  apply pro2 s a pro3 a_2

--生成表現系の根付き集合は、完全表現系になっても残っている。
lemma rootedgenerator_is_rootedset (RS : RootedSets α):
  let SF := rootedsetToClosureSystem RS
  ∀ r ∈ RS.rootedsets, r ∈ rootedSetsSF SF.toSetFamily :=
by
  intro SF
  intro r hr
  dsimp [rootedSetsSF]
  dsimp [allCompatiblePairs]
  dsimp [isCompatible]
  simp_all
  have :(r.stem,r.root) ∈ allPairs SF.toSetFamily := by
    dsimp [allPairs]
    apply Finset.mem_product.mpr
    constructor
    simp
    exact (RS.inc_ground r hr).1
    simp
    exact (RS.inc_ground r hr).2
  use r.stem
  use r.root
  constructor
  · simp
  · constructor
    · exact this
    · constructor
      · exact r.root_not_in_stem
      · intro t st rts
        simp_all only [SF]
        apply rootedpair_compatible RS t st
        · simp_all only
        · exact rts

lemma stem_is_upward_closed (SF: ClosureSystem α) :
let RS := rootedSetsFromSetFamily SF.toSetFamily
∀ (r r':ValidPair α) , r ∈ RS.rootedsets → r.root =r'.root → r.stem ⊆ r'.stem → r'.stem ⊆ SF.ground → r'∈ RS.rootedsets :=
by
  intro RS r r' hr hroot hstem sfg
  dsimp [RS]
  dsimp [rootedSetsFromSetFamily]
  dsimp [rootedSetsSF]
  dsimp [allCompatiblePairs]
  simp
  have : (r'.stem, r'.root) ∈ allPairs SF.toSetFamily :=
  by
    dsimp [allPairs]
    simp
    constructor
    · exact sfg
    · rw [←hroot]
      exact (RS.inc_ground r hr).2

  use r'.stem
  use r'.root
  constructor
  swap

  · constructor
    · simp_all only [RS]

    · dsimp [isCompatible]
      constructor
      ·  exact r'.root_not_in_stem

      · intro t
        intro sft
        intro steminc
        dsimp [RS] at hr
        dsimp [rootedSetsFromSetFamily] at hr
        dsimp [rootedSetsSF] at hr
        dsimp [allCompatiblePairs] at hr
        dsimp [isCompatible] at hr
        simp at hr
        obtain ⟨a,b,h,hr⟩ := hr
        let h2 := h.2.2 t sft
        have : a ⊆ t :=
        by
          subst hr
          subst hroot
          simp_all only [RS]
          obtain ⟨left, right⟩ := h
          obtain ⟨left_1, right⟩ := right
          intro x hx
          apply steminc
          exact hstem hx
        specialize h2 this
        have : b = r'.root :=
        by
          subst hr
          subst hroot
          simp_all only [RS]
        rw [this] at h2
        exact h2

  · cases r'
    simp_all only [RS]

------------------------------
----ここからは、根付き集合族の存在定理
----別ファイルに独立させてもよい。
------------------------------

--閉集合族から根つき集合族を与えるバージョン。rootedcircuitsではなく、rootedsetsを返す。
--rootedcircuits版は、rootedcircuits_setfamily。
lemma rootedset_setfamily (RS : RootedSets α) (SF:ClosureSystem α)
  --(eq:  ∀ (s : Finset α),(rootedsetToClosureSystem RS).sets s ↔ (SF.sets s)) :
 (eq:  rootedsetToClosureSystem RS = SF) :
  ∀ (s : Finset α), s ⊆ SF.ground → (¬ SF.sets s ↔ ∃ (p : ValidPair α), p ∈ RS.rootedsets ∧ p.stem ⊆ s ∧ p.root  ∈ (closureOperator SF (s.subtype (λ x => x ∈ SF.ground))).image Subtype.val ∧ p.root ∉ s) :=
   --∀ (s : Finset α), s ⊆ SF.ground → (¬ SF.sets s ↔ ∃ (p : ValidPair α), p ∈ (rootedcircuits_from_RS RS).rootedsets ∧ p.stem ⊆ s ∧ p.root  ∈ (closureOperator SF (s.subtype (λ x => x ∈ SF.ground))).image Subtype.val ∧ p.root ∉ s) :=
by
  have eqsets: ∀ (s : Finset α), (rootedsetToClosureSystem RS).sets s ↔ (SF.sets s) :=
  by
    intro s
    subst eq
    simp_all only
  have eqground: RS.ground = SF.ground :=
  by
    subst eq
    simp_all only
    simp_all only [implies_true]
    rfl
  intro s
  intro hs
  dsimp [rootedsetToClosureSystem] at eqsets
  dsimp [filteredFamily] at eqsets
  simp_all only [not_and, Decidable.not_not, Finset.mem_filter, Finset.mem_powerset]
  apply Iff.intro
  · intro a
    --specialize eqsets s
    rw [←eqsets] at a
    push_neg at a
    let ahs := a hs
    obtain ⟨p, hp⟩ := ahs
    --obtain ⟨q, hq⟩ := rootedcircuits_minimality RS p hp.1
    --use q  --極小な要素を使う。
    use p
    constructor
    · exact hp.1
    · constructor
      swap
      · constructor
        swap
        · exact hp.2.2
        · simp_all only [true_and, forall_const, not_false_eq_true, and_true]
          obtain ⟨left, right⟩ := hp
          obtain ⟨w, h⟩ := a
          obtain ⟨left_2, right⟩ := right
          obtain ⟨left_4, right_2⟩ := h
          obtain ⟨left_6, right_2⟩ := right_2
          dsimp [closureOperator]
          rw [Finset.mem_image]
          have : p.root ∈ SF.ground := by
            let rsi := (RS.inc_ground p left ).2
            rw [eqground] at rsi
            exact rsi
          use ⟨p.root, this⟩
          simp
          rw [mem_finsetIntersection_iff_of_nonempty] --ここでゴールが分かれる。
          · intro f hf
            rw [Finset.mem_filter] at hf
            let eq := ((eqsets f).mpr hf.2.1).2
            apply eq p left
            let hf22 := hf.2.2
            simp at hf22
            have sf: s ⊆ f := by
              rename_i eq_1
              subst eq_1
              obtain ⟨left_1, right_1⟩ := hf
              obtain ⟨left_3, right_1⟩ := right_1
              intro x hx
              apply hf22
              simp_all only [Finset.mem_map, Finset.mem_subtype, Function.Embedding.coeFn_mk, Subtype.exists,
                exists_and_left, exists_prop, exists_eq_right_right, true_and]
              exact hs hx
            exact left_2.trans sf
          · -- (Finset.filter (fun t => SF.sets t ∧ Finset.map { toFun := Subtype.val, inj' := ⋯ } (Finset.subtype (fun x => x ∈ SF.ground) s) ⊆ t)  SF.ground.powerset).Nonempty
            use SF.ground
            rw [Finset.mem_filter]
            constructor
            ·
              subst eq
              simp_all only [Finset.mem_powerset, subset_refl]
            · constructor
              · exact SF.has_ground
              ·
                subst eq
                intro x hx
                simp_all only [Finset.mem_map, Finset.mem_subtype, Function.Embedding.coeFn_mk, Subtype.exists,
                  exists_and_left, exists_prop, exists_eq_right_right]

      · --goal p.stem = s これはいえるか考えてみないとわからない。言えるかもしれないけど、今のpの取り方では条件が足りない。
        --言明を変えるか、pの取り方を変えるかする必要があり。
        subst eq
        simp_all only [forall_const]
  · intro a
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    apply Aesop.BuiltinRules.not_intro
    intro a
    --eqsetsの記述と、left_1 rightの記述が矛盾しているのでは。
    let eqsetss := (eqsets s).mpr a
    let eqsetss2 := eqsetss.2 w left
    subst eq
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, not_true_eq_false, and_false,
      eqsetss]
    obtain ⟨left_1, right_1⟩ := eqsetss
    obtain ⟨left_2, right⟩ := right
    obtain ⟨left_3, right⟩ := right
    obtain ⟨w_1, h⟩ := left_3
    simp_all only [not_true_eq_false]

--rooted_setfamilyの対偶の形
lemma rootedset_setfamily2 (RS : RootedSets α) (SF:ClosureSystem α)
  --(eq:  ∀ (s : Finset α),(rootedsetToClosureSystem RS).sets s ↔ (SF.sets s)) :
 (eq:  rootedsetToClosureSystem RS = SF) :
  ∀ (s : Finset α), s ⊆ SF.ground → (SF.sets s ↔ ¬∃ (p : ValidPair α), p ∈ RS.rootedsets ∧ p.stem ⊆ s ∧ p.root  ∈ (closureOperator SF (s.subtype (λ x => x ∈ SF.ground))).image Subtype.val ∧ p.root ∉ s) :=
by
  intro s hs
  rw [←not_iff_not]
  simp
  convert rootedset_setfamily RS SF eq s hs
  simp

lemma Finset.exists_mem_of_ne_empty {α : Type} [DecidableEq α] (s : Finset α) (h : s ≠ ∅) :
  ∃ x, x ∈ s :=
by
  rw [←Finset.nonempty_iff_ne_empty] at h
  exact h

--hyperedgeがないときの、根付きサーキットの形が与えられる。補題として使われる。
lemma ClosureSystemTheorem_mpr_lemma (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] :
 ∀ s : Finset { x // x ∈ SF.ground }, ¬ SF.sets (s.image Subtype.val) → ∀ root : { x // x ∈ SF.ground }, root ∈ (closure_operator_from_SF SF).cl s →
 (asm:root.val ∉ s.image Subtype.val) → ValidPair.mk (s.image Subtype.val) root.val asm ∈ (rootedSetsSF SF.toSetFamily) :=
by
  intro s notsf
  intro root hroot asm
  dsimp [closure_operator_from_SF] at hroot
  dsimp [rootedSetsSF]
  simp
  dsimp [allCompatiblePairs]
  simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, Finset.coe_mem,
     exists_const, Finset.mem_filter]
  obtain ⟨rootval, roottype⟩ := root
  simp_all only
  apply And.intro
  · dsimp [allPairs]
    --dsimp [Finset.product]
    have comp1: Finset.image Subtype.val s ∈ SF.ground.powerset.val := by
      simp_all only [Finset.mem_val, Finset.mem_powerset]
      simp [Finset.image_subset_iff]
    have comp2: rootval ∈ SF.ground.val := by
      simp_all only [Finset.mem_val, Finset.mem_powerset]
    exact Finset.mem_product.mpr ⟨comp1, comp2⟩

  · dsimp [isCompatible]
    constructor
    · simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const,
      not_false_eq_true]
    · intro t ht hts
      let cml := closure_monotone_lemma SF s (t.subtype (fun x => x ∈ SF.ground))
      --lemma closure_monotone_lemma {α : Type} [DecidableEq α] [Fintype α] (F : ClosureSystem α)  [DecidablePred F.sets] (s : Finset F.ground) (t : Finset F.ground) :
      --  F.sets (t.image Subtype.val) → s ⊆ t → (closure_operator_from_SF F ).cl s ⊆ t :=
      have arg1: SF.sets (Finset.image Subtype.val (Finset.subtype (fun x => x ∈ SF.ground) t)) := by
        have : t ⊆ SF.ground := by
          exact SF.inc_ground t ht
        have :Finset.image Subtype.val (Finset.subtype (fun x => x ∈ SF.ground) t) = t := by
          ext a : 1
          simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
            exists_eq_right_right, and_iff_left_iff_imp]
          intro a_1
          exact this a_1
        rw [this]
        exact ht
      have arg2: s ⊆ Finset.subtype (fun x => x ∈ SF.ground) t :=
      by
        intro x hx
        simp_all only [Finset.mem_subtype]
        obtain ⟨val, property⟩ := x
        simp_all only
        exact hts (Finset.mem_image_of_mem _ hx)
      let result := cml arg1 arg2
      --resultの内容。(closure_operator_from_SF SF).cl s ⊆ Finset.subtype (fun x => x ∈ SF.ground) t
      --hrootは、⟨rootval, roottype⟩ ∈ closureOperator SF s
      have :⟨rootval, roottype⟩ ∈ Finset.subtype (fun x => x ∈ SF.ground) t := by
        exact Finset.mem_of_subset result hroot
      simp_all only [Finset.mem_subtype]

--閉集合族とhyperedgeでない集合が与えられた時に、根つき集合が実際に存在する方の補題。
lemma ClosureSystemTheorem_mpr_lemma2 (SF : ClosureSystem α)  [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] :
 ∀ s : Finset { x // x ∈ SF.ground }, ¬ SF.sets (s.image Subtype.val) → ∃ root ∈ (closure_operator_from_SF SF).cl s,
root.val ∉ s.image Subtype.val ∧ ((asm:root.val ∉ s.image Subtype.val ) →
(ValidPair.mk (s.image Subtype.val) root.val asm) ∈ (rootedSetsSF SF.toSetFamily)) :=
by
  intro s notsf
  dsimp [closure_operator_from_SF]
  dsimp [rootedSetsSF]
  simp
  dsimp [allCompatiblePairs]
  simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, Finset.coe_mem,
    exists_const, Finset.mem_filter]

  have : ((closure_operator_from_SF SF).cl s) \ s ≠ ∅ := by
    have sneq :((closure_operator_from_SF SF).cl s) ≠ s := by
      intro a
      contrapose! notsf
      exact idempotent_from_SF_finset_lem_mpr SF s a
    have sinc: s ⊆ ((closure_operator_from_SF SF).cl s) := by
      exact extensive_from_SF_finset SF s
    --以下、大した証明でもないのに長い。短くできないか。
    rw [ne_eq,Finset.ext_iff] at sneq
    simp_rw [Finset.subset_iff] at sinc
    push_neg at sneq
    simp_all only [implies_true, Subtype.forall, Subtype.exists, ne_eq, Finset.sdiff_eq_empty_iff_subset]
    obtain ⟨w, h⟩ := sneq
    obtain ⟨w_1, h⟩ := h
    apply Aesop.BuiltinRules.not_intro
    intro a
    cases h with
    | inl h_1 =>
      obtain ⟨left, right⟩ := h_1
      apply right
      simp_all only
      apply right
      simp_all only
      tauto
    | inr h_2 =>
      obtain ⟨left, right⟩ := h_2
      simp_all only [not_true_eq_false]

  match Finset.exists_mem_of_ne_empty ((closure_operator_from_SF SF).cl s \ s) this with
  | ⟨root, hroot⟩ =>
    have root_not_in_s : root ∉ s := by
      simp_all only [Finset.mem_sdiff, not_false_eq_true]
    use root
    constructor
    ·
      simp_all only [implies_true, ne_eq, Finset.sdiff_eq_empty_iff_subset, Finset.mem_sdiff, not_false_eq_true,
        and_true, Subtype.coe_eta, forall_const, true_and]
      obtain ⟨rootval, roottype⟩ := root
      simp_all only
      apply And.intro
      · exact hroot
      · apply And.intro
        ·
          simp [allPairs]
          --apply Finset.mem_product.2
          simp_all only [Finset.mem_powerset, and_true]
          simp [Finset.image_subset_iff]
        · dsimp [isCompatible]
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const,
          not_false_eq_true]
          simp
          intro t ht hts
          let cml := closure_monotone_lemma SF  s (t.subtype (fun x => x ∈ SF.ground))
          --lemma closure_monotone_lemma {α : Type} [DecidableEq α] [Fintype α] (F : ClosureSystem α) (has_empty : F.sets ∅) [DecidablePred F.sets] (s : Finset F.ground) (t : Finset F.ground) :
          --  F.sets (t.image Subtype.val) → s ⊆ t → (closure_operator_from_SF F).cl s ⊆ t :=
          have arg1: SF.sets (Finset.image Subtype.val (Finset.subtype (fun x => x ∈ SF.ground) t)) := by
            have : t ⊆ SF.ground := by
              exact SF.inc_ground t ht
            have :Finset.image Subtype.val (Finset.subtype (fun x => x ∈ SF.ground) t) = t := by
              ext a : 1
              simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
                exists_eq_right_right, and_iff_left_iff_imp]
              intro a_1
              exact this a_1
            rw [this]
            exact ht
          have arg2: s ⊆ Finset.subtype (fun x => x ∈ SF.ground) t :=
          by
            intro x hx
            simp_all only [Finset.mem_subtype]
            obtain ⟨val, property⟩ := x
            simp_all only
            exact hts (Finset.mem_image_of_mem _ hx)
          let result := cml arg1 arg2
          --resultの内容。(closure_operator_from_SF SF).cl s ⊆ Finset.subtype (fun x => x ∈ SF.ground) t
          --hrootは、⟨rootval, roottype⟩ ∈ closureOperator SF s
          have :⟨rootval, roottype⟩ ∈ Finset.subtype (fun x => x ∈ SF.ground) t := by
            exact Finset.mem_of_subset result hroot
          simp_all only [Finset.mem_subtype]

    · simp_all only [implies_true, ne_eq, Finset.sdiff_eq_empty_iff_subset, Finset.mem_sdiff, not_false_eq_true,
      and_true, Finset.coe_mem]

--こちらの補題は、根は選べない。ステムは確定している。使いにくい補題。次の_mrt_closureの方が使いやすい。
theorem RootedCircuitsTheorem_including (SF : ClosureSystem α)  [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] :
 ∀ s : Finset { x // x ∈ SF.ground }, ∀ t : Finset { x // x ∈ SF.ground }, s ⊆ t
 → ¬ SF.sets (s.image Subtype.val) → SF.sets (t.image Subtype.val) →
  ∃ root ∈ (t \ s).image Subtype.val, root ∉ s.image Subtype.val ∧
  ((asm:root ∉ s.image Subtype.val ) →
  (ValidPair.mk (s.image Subtype.val) root asm) ∈ (rootedSetsSF SF.toSetFamily)) :=
by
  intro s t hs hnsf hts
  have : ((closure_operator_from_SF SF).cl s) ⊆ t := by
    have : (closure_operator_from_SF SF).cl t = t := by
      let id := idempotent_from_SF_finset_lem SF t
      apply id
      simp_all only
    --intro x hx
    rw [←this]
    let mnt := monotone_from_SF_finset SF s t hs
    exact mnt
  let cst := ClosureSystemTheorem_mpr_lemma2 SF s hnsf
  obtain ⟨root, hroot⟩ := cst
  use root
  constructor
  · simp_all
    obtain ⟨val, property⟩ := root
    obtain ⟨left, right⟩ := hroot
    obtain ⟨left_1, right⟩ := right
    simp_all only [not_false_eq_true, forall_true_left]
    exact this left
  · constructor
    · simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
      Finset.coe_mem, exists_const, Finset.mem_filter]
      simp_all only [not_false_eq_true]
    · simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
      Finset.coe_mem, exists_const, not_false_eq_true, imp_self, and_self]

--こちらの補題は、最初に与えたxがrootになるような根付き集合の存在定理。
theorem RootedCircuitsTheorem_closure (SF : ClosureSystem α)  [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)] (x:SF.ground):
 ∀ s : Finset { x // x ∈ SF.ground }, x ∈ closureOperator SF s
  → ¬ SF.sets (s.image Subtype.val)  →
  (asm:↑x ∉ Finset.image Subtype.val s) →
  (ValidPair.mk (s.image Subtype.val) x asm) ∈ (rootedSetsSF SF.toSetFamily) :=
by
  intro s hcl hnsf hns
  dsimp [rootedSetsSF]
  dsimp [allCompatiblePairs]
  dsimp [isCompatible]
  simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, Finset.coe_mem,
    exists_const, Finset.mem_filter]
  simp
  constructor
  · dsimp [allPairs]
    --rw [Finset.product]
    apply Finset.mem_product.mpr
    constructor
    · simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, Finset.coe_mem,
        exists_const, Finset.mem_powerset]
      obtain ⟨val, property⟩ := x
      simp [Finset.image_subset_iff]
    · simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
      Finset.coe_mem, exists_const]
  · constructor
    · simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, Finset.coe_mem,
        exists_const, not_false_eq_true]
    · intro t ht hts
      let tg : t ⊆ SF.ground := by
        exact SF.inc_ground t ht
      have : closureOperator SF s ⊆ t.subtype (λ x => x ∈ SF.ground) := by
        have : s ⊆ (t.subtype (λ x => x ∈ SF.ground)) := by
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
            Finset.coe_mem, exists_const]
          obtain ⟨val, property⟩ := x
          intro x hx
          simp_all only [Finset.mem_subtype]
          obtain ⟨val_1, property_1⟩ := x
          simp_all only
          apply hts
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_const]
        let mnt := monotone_from_SF_finset SF s (t.subtype (λ x => x ∈ SF.ground)) this
        have :SF.sets (Finset.image Subtype.val (Finset.subtype (fun x => x ∈ SF.ground) t)) :=
        by
          have :Finset.image Subtype.val (Finset.subtype (fun x => x ∈ SF.ground) t) = t :=
          by
            simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
              Finset.coe_mem, exists_const]
            obtain ⟨val, property⟩ := x
            ext a : 1
            simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
              exists_eq_right_right, and_iff_left_iff_imp]
            intro a_1
            exact tg a_1
          rw [this]
          exact ht
        have :t.subtype (λ x => x ∈ SF.ground) = closureOperator SF (Finset.subtype (fun x => x ∈ SF.ground) t) :=
        by
          let idem := idempotent_from_SF_finset_lem SF (t.subtype (λ x => x ∈ SF.ground)) this
          simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
            Finset.coe_mem, exists_const, idem]
        rw [this]
        exact mnt
      let fm := Finset.mem_of_subset this hcl
      simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta,
        Finset.coe_mem, exists_const]
      obtain ⟨val, property⟩ := x
      simp_all only
      simpa using fm

------------------------------
----ここからは、閉集合族と根付きサーキットの表現の同値性について
----別ファイルに独立させてもよい。
--閉集合族から初めて、RSを経て、集合が等しくなることが主要な結果。
------------------------------

--閉集合族が与えられたときに、根付き集合族を考えて、それから集合族の定義すると元に戻る。の片側。
--逆方向の言明は、ClosureSystemTheorem_mprで証明済みなので、実際には必要十分条件。
theorem ClosureSystemTheorem (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  ∀ s : Finset α, SF.sets s → (rootedsetToClosureSystem (rootedSetsFromSetFamily SF.toSetFamily)).sets s :=
  by
    intro s hs
    dsimp [rootedsetToClosureSystem, rootedSetsFromSetFamily]
    dsimp [filteredFamily]
    simp_all

    constructor
    · intro p hp
      have : p ∈ SF.ground :=
      by
        have :s ⊆ SF.ground := by
          exact SF.inc_ground s hs
        exact this hp
      exact this

    · dsimp [rootedSetsFromSetFamily]
      dsimp [rootedSetsSF]
      dsimp [allCompatiblePairs]
      intro p hp
      apply ClosureSystemLemma SF
      · exact hs --なぜか上にもってこれない。
      · exact hp

--集合族が与えられた時に、そこから作った根つき集合から作った集合族の集合が、元の集合であることの定理。上の補題を使って証明した。
--ClosureSystemTheoremと合わせて、必要十分条件になっている。
theorem ClosureSystemTheorem_mpr (SF : ClosureSystem α)[DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  ∀ s : Finset SF.ground, (rootedsetToClosureSystem (rootedSetsFromSetFamily SF.toSetFamily)).sets (s.image Subtype.val) → SF.sets (s.image Subtype.val) :=
by
  intro s hs
  dsimp [rootedsetToClosureSystem] at hs
  dsimp [filteredFamily] at hs
  simp_all only [not_and, Decidable.not_not, Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, Subtype.exists,
    exists_and_right, exists_eq_right]
  obtain ⟨left, right⟩ := hs
  contrapose right
  push_neg
  obtain ⟨root, hroot⟩ := ClosureSystemTheorem_mpr_lemma2 SF s right
  have arg: root.val ∉ s.image Subtype.val := by
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, Finset.coe_mem,
      exists_const, not_false_eq_true]
  let v := ValidPair.mk (s.image Subtype.val) root arg
  use v
  constructor
  ·
    simp_all only [not_false_eq_true, forall_true_left, true_and, v]
    obtain ⟨val, property⟩ := root
    obtain ⟨left_1, right_1⟩ := hroot
    simp_all only
    exact right_1
  · constructor
    · simp_all only [not_false_eq_true, forall_true_left, true_and, subset_refl]
      simp_all only [subset_refl, v]
    · intro x
      simp_all only [not_false_eq_true, forall_true_left, true_and, Subtype.coe_eta]
      --simp_all only [Finset.coe_mem]
      obtain ⟨val, property⟩ := root
      obtain ⟨left_1, right_1⟩ := hroot
      simp_all only
      apply Aesop.BuiltinRules.not_intro
      intro a
      apply right
      simp_all only
      exact arg (Finset.mem_image_of_mem _ a)

--ClosureSystemを出発点とした、根付きサーキットをとって、また集合族を考えると戻る定理。
--これまで証明した言明を使って、構造体として等しいことを示している。
lemma closuresystem_rootedsets_eq (SF:ClosureSystem α)[DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  let RS := rootedSetsFromSetFamily SF.toSetFamily
  rootedsetToClosureSystem RS = SF :=
by
  let RS := rootedSetsFromSetFamily SF.toSetFamily
  simp
  --sの範囲はsubtypeにすべきか？
  have eqsets: ∀ (s : Finset α), s ⊆ SF.ground → ((rootedsetToClosureSystem RS).sets s ↔ (SF.sets s)) :=
  by
    intro s hs
    apply Iff.intro
    · intro a
      let result := ClosureSystemTheorem_mpr SF (s.subtype (λ x => x ∈ SF.ground))
      have resultval: (rootedsetToClosureSystem (rootedSetsFromSetFamily SF.toSetFamily)).sets s → SF.sets s :=
      by
        simp at result
        intro a_1
        simp_all only [RS]
        have imp:(rootedsetToClosureSystem (rootedSetsFromSetFamily SF.toSetFamily)).sets s → (rootedsetToClosureSystem (rootedSetsFromSetFamily SF.toSetFamily)).sets (Finset.image Subtype.val (Finset.subtype (fun x => x ∈ SF.ground) s)) :=
        by
          intro a
          simp_all only
          convert a
          ext a_1 : 1
          simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
            exists_eq_right_right, and_iff_left_iff_imp]
          intro a_2
          exact hs a_2
        have : Finset.image Subtype.val (Finset.subtype (fun x => x ∈ SF.ground) s) = s := by
          ext a
          simp only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right, and_iff_left_iff_imp]
          intro a_2
          simp_all only [forall_const]
          exact hs a_2
        rw [←this]
        exact result (imp a_1)

      have :(rootedsetToClosureSystem (rootedSetsFromSetFamily SF.toSetFamily)).sets (Finset.image Subtype.val (Finset.subtype (fun x => x ∈ SF.ground) s)) :=
      by
        simp_all only [forall_const, RS]
        convert a
        ext a_1 : 1
        simp_all only [Finset.mem_image, Finset.mem_subtype, Subtype.exists, exists_and_left, exists_prop,
          exists_eq_right_right, and_iff_left_iff_imp]
        intro a_2
        exact hs a_2

      simp_all only [forall_const, RS]

    · exact ClosureSystemTheorem SF s

  let ground := SF.ground
  let inc_ground := SF.inc_ground
  let set := SF.sets

  ext --closureに@extにつけた。extすることにより、各成分ごとに等しいことを示す。

  simp_all only [RS]
  rfl --ここはgroundが等しいことを示している。

  rename_i s--sを復活させた。この辺りはかなり強引に証明している。やっていることがいまいちわからない。

  apply Iff.intro
  · intro a
    have : s ⊆ ground := by
      have : (rootedsetToClosureSystem (rootedSetsFromSetFamily SF.toSetFamily)).sets s := by
        simp_all only [RS]
      exact (rootedsetToClosureSystem (rootedSetsFromSetFamily SF.toSetFamily)).inc_ground s this
    simp_all only [RS, ground, inc_ground]
  · intro a
    have : SF.sets s:= by
      simp_all only [RS, ground, inc_ground]
    simp_all only [RS, ground, inc_ground]

------------------------------
----ここからは根付き集合と閉包システムの同値性を利用した補題
------------------------------

--ステムのclosureを取ると、根が含まれることを示す補題。まだどこでも使っていない。
--closuresystem_rootedsets_eq を使って証明。
lemma root_stem_closure (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  let RS := rootedSetsFromSetFamily SF.toSetFamily
   ∀ r:ValidPair α, (hr:r ∈ RS.rootedsets)→
  let r_sub := rootedpair_to_subtype RS r hr
  r_sub.root ∈ closureOperator SF r_sub.stem :=
by
  simp
  intro r hr
  let RS := rootedSetsFromSetFamily SF.toSetFamily
  let r_sub := rootedpair_to_subtype RS r hr
  let mc := mem_closure_iff_lemma SF r_sub.stem r_sub.root
  dsimp [r_sub] at mc
  dsimp [rootedpair_to_subtype] at mc --これをなくすと後ろでエラー
  apply mc.mpr
  intro f hf sfs

  --下で使っている。
  have r_rooted: r ∈ RS.rootedsets := by
    simp_all only [RS]

  have eq : SF = rootedsetToClosureSystem RS := by
    exact (closuresystem_rootedsets_eq SF).symm

  let tmp:= rootedpair_compatible RS (Finset.image Subtype.val f)
  --dsimp [RS] at this
  have : (rootedsetToClosureSystem RS).sets (Finset.image Subtype.val f) := by
    simp_all only [RS]
  let tmp2:= tmp this r r_rooted
  have : r.stem ⊆ Finset.image Subtype.val f := by
    intro x hx
    simp_all only [Finset.mem_image,  Subtype.exists]
    simp
    dsimp [rootedsetToClosureSystem]

    --すぐ下で暗黙に使っている。
    have :x ∈ RS.ground := by
      have: r.stem ⊆ RS.ground := by
        exact (RS.inc_ground r r_rooted).1
      exact this hx
    simp_all only [exists_true_left, RS]
    apply hf
    simp_all only [Finset.mem_subtype]

  let tmp3 := tmp2 this
  --have : r.root ∈ SF.ground := by
  --  exact (RS.inc_ground r r_rooted).2
  simp at tmp3
  obtain ⟨left, right⟩ := tmp3 --このあたりの挙動はよくわからない。
  exact right

--root_stem_closureのval版。
lemma root_stem_closure_val (SF : ClosureSystem α) [DecidablePred SF.sets] [∀ s, Decidable (SF.sets s)]:
  let RS := rootedSetsFromSetFamily SF.toSetFamily
   ∀ r:ValidPair α, (hr:r ∈ RS.rootedsets)→
  let r_sub := rootedpair_to_subtype RS r hr
  r.root ∈ (closureOperator SF r_sub.stem).image Subtype.val :=

by
  intro RS
  intro r hr vp
  let rsc:= root_stem_closure SF r hr
  simp at rsc
  dsimp [rootedpair_to_subtype] at rsc
  simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, RS, vp]
  apply Exists.intro
  · exact rsc
  · exact vp.2.2

--どの根付き集合に対しても、ステムは、hyperedgeではない。closuresystem_rootedsets_eqを使って証明。
lemma stem_is_not_hyperedge(SF:ClosureSystem α) :
 r ∈ rootedSetsSF SF.toSetFamily →  ¬ SF.sets r.stem:=
by
  intro h a
  let RS := rootedSetsFromSetFamily SF.toSetFamily
  have rrs: r ∈ RS.rootedsets := by
    dsimp [RS]
    dsimp [rootedSetsFromSetFamily]
    simp_all only

  have :r.stem ⊆ SF.ground := by
    exact ((RS.inc_ground r rrs).1)

  dsimp [rootedSetsSF] at h
  dsimp [allCompatiblePairs] at h
  dsimp [isCompatible] at h

  have eq: rootedsetToClosureSystem RS = SF  :=
  by
    exact closuresystem_rootedsets_eq SF

  have : (rootedsetToClosureSystem RS).sets r.stem :=
  by
    rw [eq]
    exact a

  dsimp [rootedsetToClosureSystem] at this
  dsimp [filteredFamily] at this
  simp at this
  let pr := this.2 r rrs (by trivial)
  exact r.root_not_in_stem pr

--rootedset_setfamilyのrootの条件をゆるくした。逆方向も示した。
lemma rootedset_setfamily_cor (SF:ClosureSystem α):
  let RS := rootedSetsFromSetFamily SF.toSetFamily
 --(eq:  rootedsetToClosureSystem RS = SF) :
  ∀ (s : Finset α), s ⊆ SF.ground → (¬ SF.sets s ↔ ∃ (p : ValidPair α), p ∈ RS.rootedsets ∧ p.stem ⊆ s ∧ p.root  ∈ SF.ground ∧ p.root ∉ s) :=
by
  intro RS
  intro s hs
  apply Iff.intro
  · intro nsfs
    have eq: rootedsetToClosureSystem RS = SF :=
    by
      exact closuresystem_rootedsets_eq SF
    let rsf := (rootedset_setfamily RS SF eq s hs).mp nsfs
    obtain ⟨p,hp1,hp2,hp3,hp4⟩ := rsf
    use p
    refine ⟨hp1,hp2,?_,hp4⟩
    simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, RS]
    obtain ⟨w, h⟩ := hp3
    simp_all only
  · intro a
    obtain ⟨p,hp1,hp2,hp3,hp4⟩ := a
    have eq: rootedsetToClosureSystem RS = SF :=
    by
      exact closuresystem_rootedsets_eq SF
    let rsf := (rootedset_setfamily RS SF eq s hs).mpr

    refine rsf ⟨p,hp1,hp2,?_,hp4⟩
    let rsc := root_stem_closure_val SF p hp1
    simp
    use hp3
    simp at rsc
    obtain ⟨rscv,rsc⟩ := rsc
    dsimp [rootedpair_to_subtype] at rsc
    have : (Finset.subtype (fun x => x ∈ (rootedSetsFromSetFamily SF.toSetFamily).ground) p.stem) ⊆ (Finset.subtype (fun x => x ∈ SF.ground) s):=
    by
      simp_all only [RS]
      exact Finset.subtype_mono hp2
    let mn := monotone_from_SF_finset SF (Finset.subtype (fun x => x ∈ (rootedSetsFromSetFamily SF.toSetFamily).ground) p.stem) (Finset.subtype (fun x => x ∈ SF.ground) s) this
    exact mn rsc

--rootedset_setfamiy_corの対偶の形。
lemma rootedset_setfamily_cor_cont (SF:ClosureSystem α):
  let RS := rootedSetsFromSetFamily SF.toSetFamily
 --(eq:  rootedsetToClosureSystem RS = SF) :
  ∀ (s : Finset α), s ⊆ SF.ground → (SF.sets s ↔ ¬ ∃ (p : ValidPair α), p ∈ RS.rootedsets ∧ p.stem ⊆ s ∧ p.root  ∈ SF.ground ∧ p.root ∉ s) :=
by
  intro RS
  intro s hs
  apply Iff.intro
  · intro nfs
    by_contra h_contra
    exact  ((rootedset_setfamily_cor SF s hs).mpr h_contra) nfs
  · intro a
    by_contra h_contra
    let rsc := (rootedset_setfamily_cor SF s hs).mp h_contra
    simp_all only [not_true_eq_false, RS, rsc]
