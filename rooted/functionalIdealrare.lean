import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
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

variable {α : Type} [Fintype α] [DecidableEq α]

instance subtype_decidable_eq {p : α → Prop} [DecidablePred p] : DecidableEq (Subtype p) :=
  fun ⟨a, ha⟩ ⟨b, hb⟩ =>
    if h : a = b then isTrue (Subtype.ext h)
    else isFalse (fun H => absurd (congrArg Subtype.val H) h)


noncomputable def setoid_ideal_injection_domain (s : Setup_spo α)(q : Quotient s.setoid ): Finset (Finset s.V) :=
   s.V.attach.powerset.filter (fun (ss:Finset s.V) => (spo_closuresystem s).sets (ss.image Subtype.val)  ∧ (classOf s q) ⊆ ss)

noncomputable def setoid_ideal_injection_codomain (s : Setup_spo α)(q : Quotient s.setoid ) : Finset (Finset s.V) :=
   s.V.attach.powerset.filter (fun (ss:Finset s.V) => (spo_closuresystem s).sets (ss.image Subtype.val)  ∧ ¬(classOf s q) ⊆ ss)

noncomputable def setoid_ideal_injection (s: Setup_spo α)(q : Quotient s.setoid ) (hm: isMaximal_spo s q) : setoid_ideal_injection_domain s q → setoid_ideal_injection_codomain s q :=
  fun ⟨ss, hss⟩ => ⟨ss \ (classOf s q), by
  dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain]
  rw [Finset.filter, Finset.powerset]
  simp
  have hss_dom : ss ∈ setoid_ideal_injection_domain s q := by
    exact hss
  have h_subset : ss ⊆ s.V.attach := by
    apply Finset.mem_powerset.mp
    simp_all only [Finset.mem_powerset]
    intro x hx
    simp_all only [mem_attach]

  dsimp [setoid_ideal_injection_domain] at hss
  rw [Finset.mem_filter] at hss
  dsimp [spo_closuresystem] at hss
  obtain ⟨hss, hss'⟩ := hss --分解できないのはimpliesの形式かも。
  --hss'は、domainに入っているideal全体か。
  obtain ⟨hss', hss''⟩ := hss'
  --この段階で、hss'は、idealの要素になる条件がはいっている。
  obtain ⟨sqq', hss'''⟩ := hss'
  --sqq'は、idealの要素となるquotientの集合。
  simp at hss'''
  obtain ⟨hss''', hss5⟩ := hss'''
  obtain ⟨hss5, hss6⟩ := hss5
  have :Finset.image Subtype.val ss ⊆ s.V := by
    simp_all only [Finset.mem_powerset, forall_true_left, mem_sdiff, true_and, Quotient.eq, and_true]
  specialize hss6 this
  obtain ⟨h_to, h_from⟩ := hss6

  constructor
  · use (ss \ classOf s q).val

    have diff_subset : ss \ classOf s q ⊆ s.V.attach := by
      intro x hx
      simp_all only [mem_sdiff, mem_attach]
    constructor
    · apply congrFun rfl
    · exact val_le_iff_val_subset.mpr diff_subset
  · constructor
    · --qを除いてもidealであることを示す必要。ここの部分は、極大性を利用する必要がある。
      dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain]
      dsimp [spo_closuresystem]
      --qの生成するidealをuseすればよいか。でも連結とは限らない。
      --ssに対応するQuotientをuseすればよいか。
      --Setup_spoにおいて、ssに対して、そのQuotientの集合を与える関数を作ってもいいかも。
      use QuotientOf s (ss \ (classOf s q))
      constructor
      · intro qq hqq q' hq'
        dsimp [QuotientOf]
        dsimp [QuotientOf] at hqq
        rw [Finset.mem_image] at hqq
        rw [Finset.mem_image]
        use Quotient.out q'
        constructor
        · --hq'から言えるはず。hq' : q' ≤ qq
          show q'.out ∈ ss \ classOf s q
          rw [Finset.mem_sdiff]
          obtain ⟨w, hqq⟩ := hqq
          obtain ⟨left, right⟩ := hqq
          rw [@mem_sdiff] at left
          have :s.setoid.r w qq.out := by
            apply s.setoid.trans (s.setoid.refl w)
            exact Quotient.mk_eq_iff_out.mp right
            --f_fromが関係ありそう。

          have qqs:qq ∈ sqq' := by
            simp_all only [Finset.mem_powerset, coe_mem, Subtype.coe_eta, Quotient.eq, forall_const]
            subst right
            simp_all only [coe_mem, Subtype.coe_eta, Quotient.eq, forall_const]
          specialize h_from
          have : qq.out ∈ ss := by
            specialize h_from qq
            rename_i x this_1 this_2
            subst right
            simp_all only [Finset.mem_powerset, Subtype.coe_eta, true_and, coe_mem, Quotient.eq]
            obtain ⟨val_1, property_1⟩ := w
            apply h_from
            · simp_all only [forall_const]
            · simp_all only [forall_const, Subtype.coe_eta]
              obtain ⟨val, property⟩ := this_1
              symm
              exact this
          have qsq:q' ∈ sqq' := by
            exact hss''' qq qqs q' hq'


          constructor
          · show q'.out ∈ ss
            specialize h_from q'
            specialize  h_from qsq
            subst right
            simp_all only [Finset.mem_powerset, coe_mem, Subtype.coe_eta, Quotient.out_eq]
          · show q'.out ∉ classOf s q
            --goal q'.out ∉ classOf s q
            --left : w ∈ ss ∧ w ∉ classOf s q
            -- hq' : q' ≤ qq
            -- right : ⟦w⟧ = qq
            -- hm : isMaximal_spo s q
            dsimp [isMaximal_spo] at hm
            have qneq:q' ≠ q := by
              intro h_contra
              have :qq = q := by
                rw [h_contra] at hq'
                have qq_q: s.spo.le qq q := by
                  apply (hm qq)
                  subst right h_contra
                  simp_all only [Finset.mem_powerset, coe_mem, Subtype.coe_eta]
                have q_qq:s.spo.le q qq := by
                  subst right h_contra
                  simp_all only [Finset.mem_powerset, coe_mem, Subtype.coe_eta]
                apply s.spo.le_antisymm
                · subst right h_contra
                  simp_all only [Finset.mem_powerset, coe_mem, Subtype.coe_eta]
                · exact hq'
              --rw [←this] at h_contra
              --rightとleftに矛盾することをいう。
              rw [←right] at this
              rw [←this] at left
              let left2 := left.2
              simp  at left2
              dsimp [classOf] at left2
              rw [Finset.mem_filter] at left2
              simp at left2
            intro h_contra
            dsimp [classOf] at h_contra
            rw [Finset.mem_filter] at h_contra
            have : q=q' := by
              subst right
              simp_all only [Finset.mem_powerset, ne_eq, mem_attach, Quotient.out_eq, and_false]
            rw [this] at qneq
            contradiction
        · simp_all only [Subtype.exists, Quotient.out_eq]
      · --(ss \ classOf s q).valがidealの要素であることを示す。
        simp
        constructor
        ·
          rename_i x
          obtain ⟨val, property⟩ := x
          intro x hx
          simp_all only [Finset.mem_image, mem_sdiff, Subtype.exists, exists_and_right, exists_eq_right]
          obtain ⟨w, h⟩ := hx
          obtain ⟨left, right⟩ := h
          simp_all only
        · intro hs
          --idealの要素になるためには、下のものがssにはいることと、
          constructor
          · intro x hx h
            dsimp [QuotientOf]
            rw [Finset.mem_image]
            use ⟨x, hx⟩
            constructor
            · simp_all only [mem_sdiff, not_false_eq_true, and_self]
            · simp_all only

          · --ssの元の同値類を考えて、その要素を持ってきたら、またssの要素。大小は関係ないかも。qが極大であることも使わないかも。
            intro q_1 hq_1 a ha hha
            specialize h_from q_1  --これは正しいのか。
            dsimp [QuotientOf] at hq_1
            rw [Finset.mem_image] at hq_1
            obtain ⟨w, hq_1⟩ := hq_1
            rw [@mem_sdiff] at hq_1
            dsimp [isMaximal_spo] at hm
            specialize hm q_1
            have srwa: (s.setoid).r w ⟨a, ha⟩:= by
              subst hha
              simp_all only [mem_sdiff, true_and, Quotient.eq]
            have : q_1 ∈ sqq' := by
              specialize h_to w
              subst hha
              simp_all only [Finset.mem_powerset, coe_mem, Subtype.coe_eta, forall_const, Quotient.eq, true_and,
                and_true]

            constructor
            · --hhaとhq_1を使う。hha : ⟦⟨a, ha⟩⟧ = q_1。hq_1 : w ∈ ss \ classOf s q ∧ ⟦w⟧ = q_1。必要であれば補題を作る。ssはsetoidで閉じている。
              --h_fromも使うかも。
              show ⟨a, ha⟩ ∈ ss
              have wss: w ∈ ss := by
                exact hq_1.1.1

              rename_i x this_1
              subst hha
              simp_all only [Subtype.coe_eta, Finset.mem_powerset, mem_sdiff, Quotient.eq, true_and, and_true,
                forall_const]
              apply h_from
              rfl

            · show ⟨a, ha⟩ ∉ classOf s q
              dsimp [classOf]
              rw [Finset.mem_filter]
              simp
              show ¬Quotient.mk'' ⟨a, ha⟩ = q
              --hq_1 : w ∈ ss \ classOf s q ∧ ⟦w⟧ = q_1は使いそう。
              --srwa: (s.setoid).r w ⟨a, ha⟩:= by
              have : q_1 ≠ q := by
                intro h_contra
                obtain ⟨hq_11, hq_12⟩ := hq_1
                rw [←h_contra] at hq_11
                rw [←hq_12] at hq_11
                dsimp [classOf] at hq_11
                rw [Finset.mem_filter] at hq_11
                simp at hq_11
              subst hha
              simp_all only [Finset.mem_powerset, Quotient.eq, forall_const, Subtype.coe_eta, true_and, and_true,
                ne_eq, not_false_eq_true]

    · have :(classOf s q).Nonempty := by --使っているみたい。
        exact classOf_nonempty s q
      rw [@subset_sdiff]
      simp_all only [disjoint_self, Finset.bot_eq_empty, not_and]
      intro a
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      simp_all only [Finset.not_nonempty_empty, disjoint_self, Finset.bot_eq_empty, not_and]
⟩

theorem setoid_ideal_injection_injective
  (s : Setup_spo α) (q : Quotient s.setoid) (hm : isMaximal_spo s q) :
  Function.Injective (setoid_ideal_injection s q hm) := by
  intro ⟨ss₁, h₁⟩ ⟨ss₂, h₂⟩ h_eq
  simp only [setoid_ideal_injection] at h_eq

  -- 差集合が等しい → 元の集合が等しいことを示す
  -- ss₁ = (ss₁ \ classOf s q) ∪ classOf s q

  have h₂_subset : classOf s q ⊆ ss₂ := by
    dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain] at h₂
    dsimp [spo_closuresystem] at h₂
    dsimp [classOf]
    simp_all only [Subtype.mk.injEq]  --場所を変えるとエラー。
    simp_all
    obtain ⟨left, right⟩ := h₂
    obtain ⟨left_1, right⟩ := right
    obtain ⟨w, h⟩ := left_1
    obtain ⟨left_1, right_1⟩ := h
    obtain ⟨left_2, right_1⟩ := right_1
    simp_all only [forall_true_left]
    obtain ⟨left_3, right_1⟩ := right_1
    exact right


  have h₁_subset : classOf s q ⊆ ss₁ := by
    dsimp [classOf]
    dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain] at h₁
    dsimp [spo_closuresystem] at h₁
    simp_all only [Subtype.mk.injEq]
    simp_all
    obtain ⟨left, right⟩ := h₁
    obtain ⟨left_1, right⟩ := right
    obtain ⟨w, h⟩ := left_1
    obtain ⟨left_1, right_1⟩ := h
    obtain ⟨left_2, right_1⟩ := right_1
    simp_all only [forall_true_left]
    obtain ⟨left_3, right_1⟩ := right_1
    exact right

  have h₁_union : ss₁ = (ss₁ \ classOf s q) ∪ (classOf s q) :=
  by
    symm
    apply Finset.sdiff_union_of_subset
    dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain] at h₁
    simp_all only [Subtype.mk.injEq]

  -- Finset.sdiff_union_of_subset : A = (A \ B) ∪ B  (if B ⊆ A)
  have eq₂ : ss₂ = (ss₂ \ classOf s q) ∪ classOf s q :=
  by
    exact Eq.symm (sdiff_union_of_subset h₂_subset)

  -- ここで eq_sdiff を使い、差集合が等しいので右辺も等しくなる
  have : ss₁ = ss₂ := by
    rw [h₁_union]
    rw [eq₂]
    have :ss₁ \ classOf s q  = ss₂ \ classOf s q := by
      rw [@Subtype.mk_eq_mk] at h_eq
      exact h_eq
    rw [this]

  exact Subtype.mk_eq_mk.mpr this

omit [Fintype α] [DecidableEq α] in
lemma powerset_image {α β : Type*}[DecidableEq β]
  (s : Finset α) (f : α → β) :
  s.powerset.image (fun a => a.image f) = (s.image f).powerset := by
  -- 要素レベルで等しいことを示すために `ext t` で両辺のメンバーシップを比較
  ext t
  --simp only [mem_image, mem_powerset]
  constructor
  · -- (→) もし `t` が左辺に属するなら
    intro a
    simp_all only [Finset.mem_image, Finset.mem_powerset]
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    subst right
    rw [Finset.image_subset_iff]
    intro x a
    simp_all only [Finset.mem_image]
    exact ⟨x, left a, rfl⟩
  · -- (←) もし `t` が右辺に属するなら
    intro ht
    -- t ⊆ s.image f
    -- このとき「t = ある a の像 `a.image f`」となる部分集合 a ⊆ s を作ればよい
    let a := s.filter (fun x => f x ∈ t)
    rw [Finset.mem_image]
    use a
    constructor
    · -- a ⊆ s は自明
      apply mem_powerset.mpr
      simp_all only [Finset.mem_powerset, filter_subset, a]
    · -- a.image f = t を示す
      ext y
      --simp only [mem_image, mem_filter]
      constructor
      -- (⇒) y ∈ a.image f → y ∈ t
      ·
        intro a_1
        simp_all only [Finset.mem_powerset, Finset.mem_image, mem_filter, a]
        obtain ⟨w, h⟩ := a_1
        obtain ⟨left, right⟩ := h
        obtain ⟨left, right_1⟩ := left
        subst right
        simp_all only [a]

      -- (⇐) y ∈ t → y ∈ a.image f
      · intro hy
        -- y ∈ t かつ t ⊆ s.image f なので y = f x の形で x ∈ s
        -- x を a に入れれば y = f x ∈ a.image f
        -- ただし「f x ∈ t」であることが a へのフィルタ条件

        have : y ∈ s.image f := by
          simp_all only [Finset.mem_powerset, Finset.mem_image, a]
          simpa [a] using ht hy--mem_of_mem_powerset ht hy
        obtain ⟨x, hx_s, rfl⟩ := mem_image.mp this
        simp_all only [Finset.mem_powerset, Finset.mem_image, mem_filter, a]
        obtain ⟨w, h⟩ := this
        obtain ⟨left, right⟩ := h
        use x

lemma card_filter_image_image_eq_filter
  {α β : Type} [DecidableEq α] [DecidableEq β]
  {s : Finset α} (f : α → β) (p : Finset β → Prop) [DecidablePred p] :
  ((s.powerset.image (Finset.image f)).filter p).card =
    ((s.image f).powerset.filter p).card := by
  rw [@filter_image]
  rw [←@powerset_image α β _ s f]
  simp only [filter_image]

lemma filter_set_of_set_comp_eq_image_filter
  {α β : Type*} [DecidableEq α] [DecidableEq β]
  (S : Finset (Finset α)) (f : Finset α → Finset β)
  (p : Finset β → Prop) [DecidablePred p] :
  (S.filter (fun s => p (f s))).image f = (S.image f).filter p := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hs, hps⟩
    obtain ⟨left, right⟩ := hps
    obtain ⟨left, right_1⟩ := left
    subst right
    simp_all only [and_true]
    exact ⟨_, left, rfl⟩
  · intro a
    obtain ⟨left, right⟩ := a
    obtain ⟨w, h⟩ := left
    obtain ⟨left, right_1⟩ := h
    subst right_1
    exact ⟨w, ⟨left, right⟩, rfl⟩

lemma card_of_image_filter_of_inj_on
  {α β : Type} [DecidableEq α] [DecidableEq β]
  (s : Finset α) (f : α → β) (p : α → Prop) [DecidablePred p]
  (hf : Set.InjOn f (s.filter p)) :
  ((s.filter p).image f).card = (s.filter p).card :=
by
  exact card_image_iff.mpr hf

lemma card_filter_image_eq
  {α β : Type} [DecidableEq α] [DecidableEq β]
  (S₀ : Finset α) (φ : α → β) (P : β → Prop)
  [DecidablePred P]
  (hφ : Set.InjOn φ (S₀.filter (fun x => P (φ x)))) :
  (S₀.filter (fun x => P (φ x))).card = ((S₀.image φ).filter P).card :=
by
  let cif := card_of_image_filter_of_inj_on S₀ φ
  simp_all only [coe_filter]
  rw [filter_image]
  simp_all only [coe_filter, cif]

lemma setoid_ideal_injection_card
  (s : Setup_spo α) (q : Quotient s.setoid) (hm : isMaximal_spo s q) :
  #(filter (fun ss => (spo_closuresystem s).sets (Finset.image Subtype.val ss)) s.V.attach.powerset) =
  #(filter (fun s_1 => (spo_closuresystem s).sets s_1) (spo_closuresystem s).ground.powerset) :=
by
  let S₀ := s.V.attach.powerset                       -- Finset s.V の部分集合たち
  let φ : Finset s.V → Finset α := fun ss => ss.image Subtype.val
  let S₁ := (spo_closuresystem s).ground.powerset     -- Finset α 上の部分集合
  let P := (spo_closuresystem s).sets                 -- closure system の性質

  change #(S₀.filter (fun s => P (φ s))) = #(S₁.filter P)

  let cfi := card_filter_image_eq S₀ φ P
  have : InjOn φ ↑(filter (fun x => P (φ x)) S₀) := by
    sorry
  specialize cfi this

  convert cfi
  dsimp [S₀, S₁, φ, P]
  have :s.V = (spo_closuresystem s).ground := by  dsimp [spo_closuresystem]
  rw [←this]
  simp_all only [coe_filter, Finset.mem_powerset, S₀, φ, S₁, P]

lemma setoid_ideal_number_of_hyperedges (s : Setup_spo α)(q : Quotient s.setoid ):
  (setoid_ideal_injection_domain s q).card + (setoid_ideal_injection_codomain s q).card =
  (spo_closuresystem s).number_of_hyperedges := by
  dsimp [setoid_ideal_injection_domain, setoid_ideal_injection_codomain]
  dsimp [SetFamily.number_of_hyperedges]
  let A := fun (ss:Finset s.V) => (spo_closuresystem s).sets (ss.image Subtype.val)
  let p := fun ss => classOf s q ⊆ ss
  let powerset := s.V.attach.powerset

  have h_part :
    (powerset.filter (fun ss => A ss ∧ p ss)).card +
    (powerset.filter (fun ss => A ss ∧ ¬p ss)).card =
    (powerset.filter A).card := by
    exact Eq.symm (add_compl_card powerset A p)

  dsimp [A, p, powerset] at h_part
  simp at h_part
  norm_cast
  rw [h_part]


  let f := fun (ss : Finset s.V) => ss.image Subtype.val

  -- A を使って書き換えたフィルター条件
  let filtered := powerset.filter A

  -- f が inj_on であることを証明
  have f_inj : Set.InjOn f filtered := by
    intros x hx y hy h_eq
    apply Finset.ext
    · intro a
      simp_all only [coe_filter, Finset.mem_powerset, mem_setOf_eq, and_true, A, p, powerset, filtered, f]
      --obtain ⟨val, property⟩ := a
      --obtain ⟨left, right⟩ := hy
      apply Iff.intro
      · intro ha
        have : a.val ∈ y.image Subtype.val := by rw [← h_eq]; exact Finset.mem_image_of_mem _ ha
        obtain ⟨a', ha', hval⟩ := Finset.mem_image.mp this
        -- a.val = a'.val ⇒ a = a' （Subtype ext）
        simp_all only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, Subtype.coe_eta, coe_mem,
          exists_const, A, p, powerset, filtered, f]

      · intro a
        search_proof

  --haveI : DecidableEq (Subtype fun x => x ∈ s.V) := inferInstance
  haveI : DecidablePred (spo_closuresystem s).sets := inferInstance
  let _inst : DecidablePred (fun x : α => x ∈ s.V) := by infer_instance --subtype_decidable_eq--Finset.decidableMem s.V;
  have cfi := @card_filter_image_image_eq_filter {x // x ∈ s.V} α inferInstance inferInstance s.V.attach Subtype.val (spo_closuresystem s).sets

  haveI : DecidablePred (spo_closuresystem s).sets := inferInstance

  have fss := filter_set_of_set_comp_eq_image_filter
        s.V.attach.powerset
        (fun (ss : Finset {x // x ∈ s.V}) => ss.image Subtype.val)
        (spo_closuresystem s).sets

  have fss2 :  (s.V.attach.powerset.filter (fun ss => (spo_closuresystem s).sets (ss.image Subtype.val))).image (fun ss => ss.image Subtype.val)
  =
  (s.V.attach.powerset.image (fun ss => ss.image Subtype.val)).filter (spo_closuresystem s).sets
  := filter_set_of_set_comp_eq_image_filter
        s.V.attach.powerset
        (fun ss => ss.image Subtype.val)
        (spo_closuresystem s).sets

  have fss_card := congrArg Finset.card fss
  #check Finset.card_image_of_injOn
  have h_card := Finset.card_image_of_injOn f_inj

  rw [← h_card]
  dsimp [filtered]
  dsimp [f]
  dsimp [A]
  simp at fss_card
  convert fss_card















  /- have fss_card :
   (filter (fun ss => (spo_closuresystem s).sets (ss.image Subtype.val)) s.V.attach.powerset).card =
    ((s.V.attach.powerset.image (fun ss => ss.image Subtype.val)).filter (spo_closuresystem s).sets).card :=
  by
  -/
  --have :s.V = (spo_closuresystem s).ground := by  dsimp [spo_closuresystem]



theorem setoid_ideal_rare (s : Setup_spo2 α)(q : Quotient (s.toSetup_spo).setoid )(hm: isMaximal_spo s.toSetup_spo q) :
  ∀ (x : classOf s.toSetup_spo q), (spo_closuresystem s.toSetup_spo).toSetFamily.is_rare x := by

  dsimp [SetFamily.is_rare]
  sorry
