import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Cover
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.StemSizeOne
import rooted.functionalCommon
--import rooted.functionalTreePreorder
import rooted.functionalTreePartialorder
import rooted.functionalSPO
import rooted.functionalSPO2
import rooted.functionalTreeIdeal

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

theorem trace_ideal_lem (s: Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x
)).card ≥ 2) :
  ∀ ss:Finset α,  (spo_closuresystem s.toSetup_spo).sets ss ↔ (spo_closuresystem (setup_trace_spo2 s x hx).toSetup_spo).sets (ss.erase x.val) := by
  --言明がおかしい。右辺からはssに自由にxを加えられる。ssがxを含まないときは両辺ともssがそのままで、ssがxを含む時は、左辺はxを含み、右辺はxを含まない。
  intro ss
  apply Iff.intro
  · intro h
    dsimp [setup_trace_spo2]
    dsimp [spo_closuresystem]
    simp
    dsimp [spo_closuresystem] at h
    obtain ⟨I,hI⟩ := h
    let I' := I.image (toNew s.toSetup_spo x hx)
    use I'
    constructor
    · --show ∀ q ∈ I', ∀ q' ≤ q, q' ∈ I'
      intro q hq q' hq'
      dsimp [I'] at hq
      dsimp [I']
      obtain ⟨hI1,hI2,hI3⟩ := hI
      specialize hI3 hI2
      obtain ⟨hI3, hI4⟩ := hI3
      rw [Finset.mem_image]
      let oldq' := toOld s.toSetup_spo x q'
      let oldq := toOld s.toSetup_spo x q

      have holdq :oldq ∈ I := by
        dsimp [oldq]
        --つかうのは、hq
        rw [Finset.mem_image] at hq
        obtain ⟨qq, hqq, hqq1⟩ := hq
        rw [←hqq1]
        let no := NewOld_id s.toSetup_spo x hx qq
        rw [no]
        exact hqq

      have :s.spo.le oldq' oldq := by
        dsimp [oldq']
        dsimp [oldq]
        exact (setup_trace_spo_le s.toSetup_spo x hx q' q).mp hq'

      have holdq' :oldq' ∈ I := by
        specialize hI1 oldq holdq oldq' this
        exact hI1

      use oldq'
      constructor
      · exact hI1 oldq holdq oldq' this
      · dsimp [oldq']
        exact OldNew_id s.toSetup_spo x hx q'

    · constructor
      ·
        simp_all only [Subtype.coe_eta, Subtype.forall]
        obtain ⟨left, right⟩ := hI
        obtain ⟨left_1, right⟩ := right
        intro q hq
        simp_all only [mem_erase, ne_eq, not_false_eq_true, true_and]
        obtain ⟨left_3, right_1⟩ := hq
        exact left_1 right_1
      · intro hs
        constructor
        · intro x1 hx1
          --goal ⟦⟨x1, ⋯⟩⟧ ∈ I'
          dsimp [I']
          rw [Finset.mem_image]
          have : x1 ∈ s.V := by
            simp_all only [Subtype.coe_eta, Subtype.forall, I']
            obtain ⟨val, property⟩ := x
            obtain ⟨left, right⟩ := hI
            obtain ⟨left_1, right_1⟩ := hx1
            obtain ⟨left_2, right⟩ := right
            simp_all only [forall_true_left]
            simp_all only
            obtain ⟨left_3, right⟩ := right
            apply left_2
            simp_all only
          use @Quotient.mk _ s.setoid ⟨x1,this⟩  --xでいいのか。x1
          constructor
          ·
            simp_all only [Subtype.coe_eta, Subtype.forall, I']
            obtain ⟨val, property⟩ := x
            obtain ⟨left, right⟩ := hI
            obtain ⟨left_1, right_1⟩ := hx1
            obtain ⟨left_2, right⟩ := right
            simp_all only [forall_true_left]
          · dsimp [toNew]
            dsimp [toErased]
            obtain ⟨val, property⟩ := x
            obtain ⟨left, right⟩ := hI
            obtain ⟨left_1, right_1⟩ := hx1
            obtain ⟨left_2, right⟩ := right
            simp_all only [forall_true_left]
            simp_all only [Subtype.coe_eta, Subtype.forall, Subtype.mk.injEq, ↓reduceDIte]
        · intro q1 hq1 x2 b hx3 --なにを証明する部分なのか考える。
          constructor
          · exact b.1
          · obtain ⟨hI1,hI2,hI3⟩ := hI
            specialize hI3 hI2
            obtain ⟨hI3, hI4⟩ := hI3
            let q1old := toOld s.toSetup_spo x q1
            specialize hI4 q1old


            dsimp [I'] at hq1
            rw [Finset.mem_image] at hq1
            obtain ⟨q, hq, hq1⟩ := hq1
            have hqold:q = toOld s.toSetup_spo x q1 := by
              --hq1 : toNew s.toSetup_spo x hx q = q1
              --の両辺にtoOld s.toSetup_spo xを作用させる。
              let no := NewOld_id s.toSetup_spo x hx q
              subst hq1
              simp_all only [Subtype.coe_eta, Subtype.forall, forall_const, I', q1old, no]


            have :q1old ∈ I := by
              dsimp [q1old]
              rw [←hqold]
              exact hq

            specialize hI4 this

            specialize hI4 ⟨x2, b.2⟩

            simp at hI4
            apply hI4

            dsimp [q1old]

            rw [←hqold]

            -- ⟦⟨x2, ⋯⟩⟧ = qをしめしたい。
            -- hqold:q = toOld s.toSetup_spo x q1
            -- hq1 : toNew s.toSetup_spo x hx q = q1
            --などが成り立っていて、qとq1は対応するもの。
            --hx3 : ⟦⟨x2, ⋯⟩⟧ = q1が成り立っている。
            rw [←hq1] at hx3
            let ca := congrArg (toOld  s.toSetup_spo x) hx3
            rw [NewOld_id s.toSetup_spo x hx q] at ca
            rw [←ca]
            dsimp [toOld]
  · intro h
    dsimp [setup_trace_spo2] at h
    dsimp [spo_closuresystem]
    simp
    dsimp [spo_closuresystem] at h
    obtain ⟨I,hI⟩ := h
    let I' := I.image (toOld s.toSetup_spo x )
    use I'
    --ssは、xを含む場合も含まない場合もどちらもある？場合分けしたほうがいい？
    constructor
    · --show ∀ q ∈ I', ∀ q' ≤ q, q' ∈ I'
      intro q hq q' hq'
      dsimp [I'] at hq
      dsimp [I']
      obtain ⟨hI1,hI2,hI3⟩ := hI
      specialize hI3 hI2
      obtain ⟨hI3, hI4⟩ := hI3
      rw [Finset.mem_image]
      let newq' := toNew s.toSetup_spo x hx q'
      let newq := toNew s.toSetup_spo x hx q
      use newq'
      constructor
      · --使うのは、hI1
        have : newq ∈ I := by
          dsimp [newq]
          rw [Finset.mem_image] at hq
          obtain ⟨qq, hqq, hqq1⟩ := hq
          rw [←hqq1]
          let no := OldNew_id s.toSetup_spo x hx qq
          rw [no]
          exact hqq
        specialize hI1 newq this
        have : (setup_trace_spo2 s x hx).toSetup_spo.spo.le newq' newq := by
          dsimp [setup_trace_spo2]

          let sts := (setup_trace_spo_le s.toSetup_spo x hx newq' newq).mpr
          apply sts
          dsimp [newq',newq]
          rw [NewOld_id s.toSetup_spo x hx q']
          rw [NewOld_id s.toSetup_spo x hx q]
          exact hq'
        simp_all only [Finset.mem_image, mem_erase, ne_eq, Subtype.coe_eta, Subtype.forall, not_false_eq_true, true_and,
          le_refl, newq, I', newq']
      · dsimp [newq']
        exact NewOld_id s.toSetup_spo x hx q'
    · obtain ⟨hI1,hI2,hI3⟩ := hI
      specialize hI3 hI2
      obtain ⟨hI3, hI4⟩ := hI3
      have hss: ss ⊆ s.V:= by
        rw [@subset_erase] at hI2
        let xp := x.property
        obtain ⟨hI2, _⟩ := hI2
        exact (erase_subset_iff_of_mem xp).mp hI2
      constructor
      · exact hss
        -- For example, you might want to assert properties of hI4 or use it in a proof

      · intro hs
        constructor
        · --Iが制限された新しい世界。I'が制限されない古い世界。
          intro x1 hx1
          --goal ⟦⟨x1, ⋯⟩⟧ ∈ I'
          dsimp [I']
          rw [Finset.mem_image]
          --x1がxに一致するケースと一致しないケースにわけたほうがいい？
          have : x1 ∈ s.V.erase x := by --これがいえるのは、ssがxを含まないケースだけかも。
            sorry
          let q' := @Quotient.mk _ (restrictedSetoid s.toSetup_spo x) x1

          let newq' := toNew s.toSetup_spo x hx           sorry
        · sorry





theorem trace_ideal (s: Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x
)).card ≥ 2) :
  ∀ ss:Finset α,  (spo_closuresystem (setup_trace_spo2 s x hx).toSetup_spo).sets ss ↔ ((spo_closuresystem s.toSetup_spo).toSetFamily.trace x.val (by simp_all only [ge_iff_le,
    coe_mem] ) (by
  have :s.V = (spo_closuresystem s.toSetup_spo).ground := by
    simp_all only [ge_iff_le]
    obtain ⟨val, property⟩ := x
    rfl
  have : s.V.card ≥ 2:= by
    let csl := card_subtype_le_original  (classOf s.toSetup_spo ⟦x⟧)
    linarith
  exact this
    )).sets ss :=  by
    intro ss
    apply Iff.intro
    · intro h
      --dsimp [setup_trace_spo2] at h
      dsimp [SetFamily.trace]
      constructor
      · --inc_groundをtうかうか？
        have : ss ⊆ s.V.erase x.val := by
          let sc := (spo_closuresystem (setup_trace_spo2 s x hx).toSetup_spo).inc_ground ss h
          simp at sc
          dsimp [setup_trace_spo2] at sc
          dsimp [spo_closuresystem] at sc
          exact sc
        rw [@subset_erase] at this
        simp_all only [not_false_eq_true]

      · --hyperedge(ideal) ssがxを含んでいたか、含んでなかったかで、場合分けする必要があるかも。
        dsimp [setup_trace_spo2] at h
        dsimp [restrictedSetoid] at h
        --spo_closuresystemは展開する必要があるのかないのか。idealかどうかは順序を見る必要があるので、展開が必要ではないか。
        --fqの議論は必要なのかどうか。親が一つであることは今回のには関係してなさそう。xの極大性もあまり関係してなくて、xを含む同値類が2以上であることが大事。
        --二つが同じになるという前に、ともに元になる集合族がある。
        --元々のideal ssがxを含む場合と含まない場合がある。xを含む同値類の大きさが2以上なので、xが極大になるが極大性は直接的には使わないかも。
        --toOldを使って証明する必要があるか。ssの同値類をtoOldで写したofClassがsssとする。
        --これがもとの親のhyperedgeで、それからxを引いたものがもとのssになる。
        sorry
    · intro h
      dsimp [setup_trace_spo2]
      dsimp [SetFamily.trace] at h
      cases h.2
      case inl hl=>
        --ssがxを含まないケース。順序集合とかidealとかまで話を戻す必要があるのか。
        dsimp [spo_closuresystem]
        dsimp [spo_closuresystem] at hl
        obtain ⟨I,hI⟩ := hl
        obtain ⟨hI1,hI2,hI3⟩ := hI
        --use I --expected Finset (Quotient (restrictedSetoid s.toSetup_spo x))
        --use I はだめ。Iを加工する必要があるのか。同値類を変換する必要がある。xを含むところだけ削ったものを作る必要がある。
        --新たにdefを作るのがいいのか。setoidの変換で、xを削ったもの。すでにあるのか。
        sorry
      case inr hr=>
        --ssがxを含むケース。
        sorry
