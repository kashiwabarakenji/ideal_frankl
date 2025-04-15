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

--制限される前から、制限された世界への成り立つ定理。
theorem trace_ideal_lem (s: Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x
)).card ≥ 2) :
  ∀ ss:Finset α,  (spo_closuresystem s.toSetup_spo).sets ss → (spo_closuresystem (setup_trace_spo2 s x hx).toSetup_spo).sets (ss.erase x.val) := by
  --右から左は別の補題に分けた。
  intro ss
  intro h
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

noncomputable def spo_equiv_x_sub (s : Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2) : Finset s.V :=
  (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).erase x

--xと同値だけど、xそのものはふくまない定義。
noncomputable def spo_equiv_x (s : Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2) : Finset α :=
  ((classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).erase x).image Subtype.val

noncomputable def spo_equiv_x_with (s : Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).card ≥ 2) : Finset α :=
  ((classOf s.toSetup_spo (@Quotient.mk _ s.setoid x))).image Subtype.val

  --s.toSetup_spo.spo.le x (spo_equiv_x s x hx) := by

--制限されたあとのhyperedgeから制限される前の世界に戻す定理。
theorem trace_ideal_lem_rev (s: Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x
)).card ≥ 2) :
  ∀ ss:Finset α, (spo_closuresystem (setup_trace_spo2 s x hx).toSetup_spo).sets ss → ((spo_equiv_x_with s x hx) ∩ ss).Nonempty  → (spo_closuresystem s.toSetup_spo).sets (ss ∪ {x.val}):= by
  sorry
  --証明の流れとしては、Nonemptyの要素を取り出して、それに映る要素がもともとの世界のhyperedge内にあって、xと同値なので、xもhyperedgeに含まれるという流れになる。

lemma new_lem_notx (s: Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x
)).card ≥ 2) :
  ∀ x_1: s.V.erase x.val, (h:x_1.val ∉ (spo_equiv_x_with s x hx)) → toNew s.toSetup_spo x hx (@Quotient.mk _ s.setoid ⟨x_1.val,by
  obtain ⟨val, property⟩ := x
  obtain ⟨val_1, property_1⟩ := x_1
  simp_all only
  simp_all only [mem_erase, ne_eq]⟩) = @Quotient.mk _ (restrictedSetoid s.toSetup_spo x) x_1 :=
by
  intro x_1 h
  dsimp [toNew]
  dsimp [spo_equiv_x_with] at h
  dsimp [classOf] at h
  dsimp [toErased]
  split
  · have :(setup_trace_spo2 s x hx).toSetup_spo.setoid.r (representativeNeSelf s.toSetup_spo x hx) x_1 := by
      rename_i h_1
      simp_all only [ge_iff_le, Quotient.eq, Subtype.val_injective, image_erase, mem_erase, ne_eq, Finset.mem_image,
        mem_filter, mem_attach, true_and, Subtype.exists, exists_and_right, exists_eq_right, exists_prop, not_and,
        Function.const_apply]
      --obtain ⟨val, property⟩ := x
      obtain ⟨val_1, property_1⟩ := x_1
      simp_all only [Subtype.mk.injEq, not_true_eq_false, forall_const, IsEmpty.forall_iff]
      --subst h_1
      dsimp [setup_trace_spo2]
      dsimp [restrictedSetoid]
      let rmc := representativeNeSelf_mem_classOf s.toSetup_spo x hx
      obtain ⟨val, property⟩ := x
      simp_all only [Subtype.mk.injEq, not_true_eq_false, forall_const, IsEmpty.forall_iff]
      subst h_1
      dsimp [representativeNeSelf]
      simp_all only
      exfalso
      simp_all only [mem_erase, ne_eq, not_true_eq_false, and_true]


    rename_i h_1
    simp_all only [Quotient.eq, Subtype.val_injective, image_erase, mem_erase, ne_eq, Finset.mem_image, mem_filter,
      mem_attach, true_and, Subtype.exists, exists_and_right, exists_eq_right, exists_prop, not_and,
      Function.const_apply, Subtype.coe_eta]

  · simp_all only [ge_iff_le, Quotient.eq, Subtype.val_injective, image_erase, mem_erase, ne_eq, Finset.mem_image,
    mem_filter, mem_attach, true_and, Subtype.exists, exists_and_right, exists_eq_right, not_and, not_exists,
    Subtype.coe_eta]

theorem trace_ideal_lem_rev2 (s: Setup_spo2 α) (x: s.V)  (hx:(classOf s.toSetup_spo (@Quotient.mk _ s.setoid x
)).card ≥ 2) :
  ∀ ss:Finset α, (spo_closuresystem (setup_trace_spo2 s x hx).toSetup_spo).sets ss → (spo_equiv_x_with s x hx) ∩ ss =∅ → (spo_closuresystem s.toSetup_spo).sets ss := by


  --証明の流れとしては、ssのもとになるhyperedgeが、xと同値であるものがないので、xを含む同値類の部分を持たずに、制限前でもそのままであることを示す。
  --ssの元になるhyperedgeはxを含まないことがわかる。
  intro ss
  intro h hn
  dsimp [setup_trace_spo2] at h

  dsimp [restrictedSetoid] at h
  -- (spo_equiv_x s x hx) ∩ ss =∅の時に成り立つ性質を補題にしたいところ。
  dsimp [spo_closuresystem]
  dsimp [spo_closuresystem] at h -- ここでdsimpを適用します。
  obtain ⟨I,hI⟩ := h
  obtain ⟨hI1,hI2,hI3⟩ := hI
  specialize hI3 hI2
  obtain ⟨hI3, hI4⟩ := hI3
  let I' := I.image (toOld s.toSetup_spo x)
  use I' --もとの言明があっていて、後半の証明が破綻しているとすると、ここが間違っている可能性がある。
  --spo_closuresystemが間違っているかもしれないし、setup_trace_spo2が間違っているかもしれないし、trace_ideal_lem_rev2の言明が間違っているかもしれない。
  --ここで、ゴールの3番目の部分が成り立たない可能性。x=xxのとき。
  constructor
  · intro q hq q' hq'
    let newq := toNew s.toSetup_spo x hx q
    let newq' := toNew s.toSetup_spo x hx q'
    have : newq ∈ I := by
      dsimp [newq]
      rw [Finset.mem_image] at hq
      obtain ⟨qq, hqq, hqq1⟩ := hq
      rw [←hqq1]
      let no := OldNew_id s.toSetup_spo x hx qq
      rw [no]
      exact hqq
    dsimp [I'] at hq
    dsimp [I']
    rw [Finset.mem_image]
    rw [Finset.mem_image] at hq
    obtain ⟨qq, hqq, hqq1⟩ := hq
    specialize hI1 newq this
    specialize hI1 newq'
    have :(setup_trace_spo2 s x hx).toSetup_spo.spo.le newq' newq := by
      sorry --こっち向きが証明しているか調べる。
    specialize hI1 this
    use newq'
    constructor
    · exact hI1
    · dsimp [newq']
      exact NewOld_id s.toSetup_spo x hx q'
  · constructor
    · sorry
    · intro hs
      constructor
      · intro x1 hx1
        --goal ⟦⟨x1, ⋯⟩⟧ ∈ I'
        dsimp [I']
        rw [Finset.mem_image]
        have : x1 ∈ s.V := by
          exact hs hx1
        --show ∃ a ∈ I, toOld s.toSetup_spo x a = ⟦⟨x1, ⋯⟩⟧
        --またnewq'を使うと思われる。
        have :x1 ∈ s.V.erase x := by
          rw [@mem_erase]
          constructor
          · exact ne_of_mem_erase (hI2 hx1)
          · simp_all only [Subtype.coe_eta, Subtype.forall, mem_erase, ne_eq, I']
        let q' := @Quotient.mk _ (restrictedSetoid s.toSetup_spo x) ⟨x1,this⟩
        use q'
        exact And.symm ⟨rfl, hI3 x1 hx1⟩

      · intro q hq xx hxx --I'に入っているqは、その要素は、ssの要素であることを示す。hI4は使いそう。
        show ↑xx ∈ ss --xx=xのときは、ゴールが証明できないのでは。

        --hI4を使って証明か？
        let newq := toNew s.toSetup_spo x hx q
        specialize hI4 newq
        have :newq ∈ I := by
          dsimp [newq]
          rw [Finset.mem_image] at hq
          obtain ⟨qq, hqq, hqq1⟩ := hq
          rw [←hqq1]
          let no := OldNew_id s.toSetup_spo x hx qq
          rw [no]
          exact hqq
        specialize hI4 this
        by_cases hnx: xx = x
        case pos =>
          subst hnx
          --これは成り立たない。矛盾じゃなくて、ゴールが証明できない。
          sorry
        case neg =>
          --xxがxと一致する場合は、ssに入る。
          /-
          have : x.val ∈ ss := by
            dsimp [ss]
            rw [@mem_erase]
            constructor
            · exact ne_of_mem_erase (hI2 hx)
            · simp_all only [Subtype.coe_eta, Subtype.forall, mem_erase, ne_eq, I']
          exact this
          -/
          have :xx.val ∈ s.V.erase ↑x  := by
            rw [@mem_erase]
            constructor
            · exact Subtype.coe_ne_coe.mpr hnx
            ·
              subst hxx
              simp_all only [Subtype.coe_eta, Finset.mem_image, Subtype.forall, mem_erase, ne_eq, coe_mem, I', newq]

           --· exact coe_mem xx

          specialize hI4 ⟨xx.val, this⟩
          apply hI4
          simp
          --show  ⟦⟨↑xx, ⋯⟩⟧ = newq
          dsimp [newq]
          --dsimp [toNew]
          --dsimp [toErased]
          --rw [←hxx]
          have :q = toOld s.toSetup_spo x newq := by
            exact Eq.symm (NewOld_id s.toSetup_spo x hx q)
          rw [this]
          rw [OldNew_id s.toSetup_spo x hx newq]
          rename_i h_1
          let nln := new_lem_notx s x hx ⟨xx.val, h_1⟩
          have : xx.val ∉ spo_equiv_x_with s x hx := by
            dsimp [spo_equiv_x_with]
            --thisからqは、newqは対応。
            --hxxからxxもqに対応。
            --hnがメインの条件。
            by_contra h_contra
            have : xx.val ∈ ss := by
              apply hI4
              --⟦⟨↑⟨↑xx, h_1⟩, ⋯⟩⟧ = newq
              dsimp [newq]
              rw [←hxx]
              simp
              dsimp [toNew]
              dsimp [toErased]
              split
              · let rmc := representativeNeSelf_mem_classOf s.toSetup_spo x hx
                --obtain ⟨val, property⟩ := x
                --obtain ⟨val_1, property_1⟩ := xx
                simp_all only [mem_erase, ne_eq]
                rename_i h_2
                rw [h_2] at h_1
                have : (restrictedSetoid s.toSetup_spo x).r (representativeNeSelf s.toSetup_spo x hx) ⟨x.val, h_1⟩ := by
                  simp_all only [ge_iff_le, Quotient.eq, Subtype.val_injective, image_erase, mem_erase, ne_eq,
                    Finset.mem_image, mem_filter, mem_attach, true_and, Subtype.exists, exists_and_right,
                    exists_eq_right, exists_prop, not_and, Function.const_apply]
                simp at this
                simp
                exact Quotient.sound (id (Setoid.symm' (restrictedSetoid s.toSetup_spo x) this))

              · exact rfl
            have :xx.val ∈ spo_equiv_x_with s x hx ∩ ss := by
              dsimp [spo_equiv_x_with]
              apply mem_inter_of_mem-- h_contra this
              exact h_contra
              exact this
            rw [hn] at this
            contradiction

          specialize nln this
          dsimp [newq]
          symm
          rw [←hxx]
          simp at nln
          simp
          rw [nln]
          exact rfl






  /-古いもの 消す。
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
  -/


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
      ·
        have : ss ⊆ s.V.erase x.val := by
          let sc := (spo_closuresystem (setup_trace_spo2 s x hx).toSetup_spo).inc_ground ss h
          simp at sc
          dsimp [setup_trace_spo2] at sc
          dsimp [spo_closuresystem] at sc
          exact sc
        rw [@subset_erase] at this
        simp_all only [not_false_eq_true]

      · --hyperedge(ideal) ssがxを含んでいたか、含んでなかったかで、場合分けする必要があるかも。
        --dsimp [setup_trace_spo2] at h
        --dsimp [restrictedSetoid] at h
        --spo_closuresystemは展開する必要があるのかないのか。idealかどうかは順序を見る必要があるので、展開が必要ではないか。
        --fqの議論は必要なのかどうか。親が一つであることは今回のには関係してなさそう。xの極大性もあまり関係してなくて、xを含む同値類が2以上であることが大事。
        --二つが同じになるという前に、ともに元になる集合族がある。
        --元々のideal ssがxを含む場合と含まない場合がある。xを含む同値類の大きさが2以上なので、xが極大になるが極大性は直接的には使わないかも。
        --toOldを使って証明する必要があるか。ssの同値類をtoOldで写したofClassがsssとする。
        --これがもとの親のhyperedgeで、それからxを引いたものがもとのssになる。
        show (spo_closuresystem s.toSetup_spo).sets ss ∨ (spo_closuresystem s.toSetup_spo).sets (ss ∪ {↑x})
        --分類するのは、xがssにはいっているかではない。ssはxを含み得ない。ssがxと同値な要素を含んでいるかどうかで分類。
        by_cases hn:((spo_equiv_x_with s x hx) ∩ ss).Nonempty
        case pos =>
          let tilr := trace_ideal_lem_rev s x hx ss
          specialize tilr h  hn
          exact Or.inr tilr
        case neg =>
          have :spo_equiv_x_with s x hx ∩ ss = ∅ := by
            exact Finset.not_nonempty_iff_eq_empty.mp hn
          --このときは、xと関係がないssであるとき。補題を作るか。
          let tilr2 := trace_ideal_lem_rev2 s x hx ss
          specialize tilr2 h this
          exact Or.inl tilr2

    · intro h
      --dsimp [setup_trace_spo2]
      dsimp [SetFamily.trace] at h
      have hh : ((classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)).erase x).Nonempty := by
        have hhx : x∈ (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)) := by
          simp_all only [ge_iff_le, coe_mem]
          obtain ⟨val, property⟩ := x
          dsimp [classOf]
          rw [Finset.mem_filter]
          constructor
          · simp_all only [mem_attach]
          · simp_all only
        let fc := Finset.card_erase_of_mem hhx
        simp only [gt_iff_lt, Nat.one_lt_iff_ne_zero_and_ne_one] at hhx
        apply Finset.card_pos.1
        simp_all only [ge_iff_le, tsub_pos_iff_lt, fc]
        obtain ⟨val, property⟩ := x
        obtain ⟨left, right⟩ := h
        simp_all only
        exact hx

      have rwss:(ss ∪ {↑x}).erase ↑x = ss := by
        --simp_all only [Subtype.coe_eta, Subtype.forall, forall_true_left]
        obtain ⟨val, property⟩ := x
        obtain ⟨left_1, right_1⟩ := h
        simp_all only
        cases right_1 with
        | inl h =>
          ext a : 1
          simp_all only [mem_erase, ne_eq, Finset.mem_union, Finset.mem_singleton]
          apply Iff.intro
          · intro a_1
            obtain ⟨left_2, right_1⟩ := a_1
            simp_all only [or_false]
          · intro a_1
            simp_all only [true_or, and_true]
            apply Aesop.BuiltinRules.not_intro
            intro a_2
            subst a_2
            simp_all only
        | inr h_1 =>
          ext a : 1
          simp_all only [mem_erase, ne_eq, Finset.mem_union, Finset.mem_singleton]
          apply Iff.intro
          · intro a_1
            obtain ⟨left_2, right_1⟩ := a_1
            simp_all only [or_false]
          · intro a_1
            simp_all only [true_or, and_true]
            apply Aesop.BuiltinRules.not_intro
            intro a_2
            subst a_2
            simp_all only

      --simp_all only [Subtype.coe_eta, Subtype.forall]
        --obtain ⟨val, property⟩ := x
        --obtain ⟨left, right⟩ := h
        --simp_all only
        --cases right with --さっきもこの場合分けを行ったのではないか？
        --| inl h => --h:(spo_closuresystem s.toSetup_spo).sets ss
          --このケースは、hxの仮定より起こり得ないことを示す。xがssに入っていれば、xの同値類の仲間も入っているはず。しかし、ssは、xを含まないので、xの仲間も含まない。
      obtain ⟨x1, hx1⟩ := hh --x1がxの同値類の仲間。
      have : s.setoid.r x1 x := by
        have : x1 ∈ (classOf s.toSetup_spo (@Quotient.mk _ s.setoid x)) := by
          simp_all only [mem_erase, ne_eq]
        dsimp [classOf] at this
        rw [Finset.mem_filter] at this
        let eq := @Quotient.eq _ s.setoid x1 x
        simp_all only [mem_erase, ne_eq, mem_attach, true_and, eq]
      cases h.2
      case inl hl=>
        --ssがxを含まないケース。(spo_closuresystem s.toSetup_spo).sets ss
        --dsimp [spo_closuresystem]
        --dsimp [spo_closuresystem] at hl
        --obtain ⟨I,hI⟩ := hl --この分解は自動的にdsimp spo_closuresystemを行ってるみたい。
        --obtain ⟨hI1,hI2,hI3⟩ := hI
        --specialize hI3 hI2
        --obtain ⟨hI3, hI4⟩ := hI3
        --use I --expected Finset (Quotient (restrictedSetoid s.toSetup_spo x))
        --use I はだめ。Iを加工する必要があるのか。同値類を変換する必要がある。xを含むところだけ削ったものを作る必要がある。
        --新たにdefを作るのがいいのか。setoidの変換で、xを削ったもの。すでにあるのか。


        --have : x1.val ∈ (ss ∪ {x.val}) := by
        --thisと、(spo_closuresystem s.toSetup_spo).sets ssから、言えるはず。
        let sce := @spo_closuresystem_equiv _ _ _ ss s.toSetup_spo x1 x this
        specialize sce hl
        have :x1.val ∉ ss:= by
          exact (iff_false_right h.1).mp sce

          --have :x.val ∉ ss := by
           --x1は、classOfから持ってきたので、x1が含まれている時は含まれている。
          --  simp_all only [mem_erase, ne_eq, not_false_eq_true]
          --矛盾が導きたかったけど、うまく導けず。
        let til := trace_ideal_lem s x hx ss
        simp at til
        have rwss2: (ss.erase ↑x) = ss := by
          simp_all only [true_or, and_true, mem_erase, ne_eq, not_false_eq_true, erase_eq_of_not_mem]
        rw [rwss2] at til
        apply til
        exact hl

      case inr hr =>
        let til := trace_ideal_lem s x hx (ss ∪ {x.val})
        simp at til
        rw [←rwss]
        apply til
        --ssがxを含むケース。
        exact hr
