--import Init.Data.Fin.Lemmas
import Mathlib.Order.Defs.PartialOrder
--import Mathlib.Order.Cover
--import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
--import LeanCopilot
import rooted.CommonDefinition
import rooted.ClosureMinors
import rooted.Preorder
import rooted.Dominant
import rooted.FamilyLemma
import rooted.functionalPartialMaximal
import rooted.functionalPartial

open Finset Set Classical

set_option maxHeartbeats 2000000

variable {α : Type} [Fintype α] [DecidableEq α]

--このファイルは半順序集合の極大要素のtraceに関するもの。連結成分の数は1とは限らない。

--ただのSetupと比較するとシンプルになっている。preorderのときのような同値類を考える必要がない。
--structure Setup_po (α : Type) [Fintype α] [DecidableEq α] where
--(V : Finset α)
--(nonemp   : V.Nonempty)
--(f : V → V)
--(po : PartialOrder V)
--(order : ∀ x y : V, (reach f x y ↔ po.le x y)) --fからpo.leが決まる。

--def reach {A : Type} (f : A → A) (x y : A) : Prop :=  ∃ n : ℕ, f^[n] x = y


--半順序の極大要素のtrace。PartialOneで使う。
def po_trace (s : Setup_po α) (x : s.V)
    (pm   : po_maximal s x)
    (geq2 : s.V.card ≥ 2) : Setup_po α := by
  classical
  -- 新しい頂点集合
  let V' : Finset α := s.V.erase x
  -- `V'` が空でないことを証明
  have nonemp' : (V' : Finset α).Nonempty := by
    -- |V| ≥ 2 なので x 以外の要素 y が存在
    have : (s.V.filter fun a : α => a ≠ x).card ≥ 1 := by
      have hcard := (show 2 ≤ s.V.card from geq2)
      have hx : (x : α) ∈ s.V := x.property
      -- 消去後のカード = card V - 1 ≥ 1
      have h₁ := (s.V.card_erase_add_one hx).symm
      have : (s.V.erase (x : α)).card + 1 = s.V.card := by
        simpa using s.V.card_erase_add_one hx
      have geq1: (s.V.erase (x : α)).card ≥ 1 := by
        have h₀ : s.V.card ≥ 2 := geq2
        have h₁ : (s.V.erase (x : α)).card + 1 = s.V.card :=
          s.V.card_erase_add_one hx
        linarith
      simp [V']
      apply Finset.card_pos.mp
      have :(filter (fun a => ¬a = ↑x) s.V) = s.V.erase ↑x := by
        ext a
        constructor
        · intro ha;
          rw [Finset.mem_erase]
          rw [Finset.mem_filter] at ha
          constructor
          · exact ha.2
          · exact ha.1
        · intro ha;
          rw [Finset.mem_erase] at ha
          rw [Finset.mem_filter]
          constructor
          · exact ha.2
          · exact ha.1
      have :#(filter (fun a => ¬a = ↑x) s.V) ≥ 1 := by
        rw [this]
        exact geq1
      exact this

    -- card > 0 ⇒ Nonempty
    simp_all [V']
    obtain ⟨val, property⟩ := x
    simp_all only
    contrapose! this
    simp_all only [not_nontrivial_iff, ne_eq, Finset.not_nonempty_iff_eq_empty]
    ext a : 1
    simp_all only [mem_filter, Finset.notMem_empty, iff_false, not_and, Decidable.not_not]
    intro a_1
    apply this
    · simp_all only [mem_coe]
    · simp_all only [mem_coe]
    --exact Finset.card_pos.mp (Nat.zero_lt_of_lt this)
  -- キャスト : V' → V
  let φ : V' → s.V := fun y =>
    ⟨(y : α), (Finset.mem_of_mem_erase y.property)⟩
  -- 逆キャスト（画像が x でないことを前提）
  have φ_inv : ∀ {z : s.V}, (z : α) ≠ x → (z : α) ∈ V' := by
    intro z hz
    have hzV : (z : α) ∈ s.V := z.property
    exact Finset.mem_erase.mpr ⟨hz, hzV⟩
  -- 新しい写像 f'
  let f' : V' → V' := fun y => by
    -- 元の写像の像
    let z : s.V := s.f (φ y)
    by_cases h : ((z : α) = x)
    -- f y = x なら自己ループ
    · exact ⟨y, y.property⟩
    -- そうでなければそのまま移す
    · exact ⟨(z : α), φ_inv (by simpa using h)⟩
  -- 制限半順序
  let le' : V' → V' → Prop := fun a b => s.po.le (φ a) (φ b)
  -- `PartialOrder` を作る（証明は元の半順序の性質を継承）
  let po' : PartialOrder V' :=
  { le := le'
    le_refl := by
      intro a; exact s.po.le_refl _
    le_trans := by
      intro a b c h₁ h₂;
      exact s.po.le_trans _ _ _ (by simpa using h₁) (by simpa using h₂)

    le_antisymm := by
      intro a b h₁ h₂
      cases a with | mk a ha' =>
      cases b with | mk b hb' =>
      dsimp [le'] at h₁ h₂
      have ha: (a : α) ∈ s.V := by
        exact mem_of_mem_erase ha'
      have hb: (b : α) ∈ s.V := by
        exact mem_of_mem_erase hb'
      have : φ ⟨a, ha'⟩ = φ ⟨b, hb'⟩ := by
        apply s.po.le_antisymm ⟨a, ha⟩ ⟨b, hb⟩
        exact h₁
        exact h₂

      simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.mk.injEq, le', V', φ]
  }
  -- reach と ≤ の同値
  have order' : ∀ y z : V', reach f' y z ↔ po'.le y z := by
    intro y z
    -- 左⇒右 grokによる証明。
    have forward : reach f' y z → le' y z := by
      rintro ⟨n, hn⟩
      have step : ∀ a : V', le' a (f' a) := by
        intro a
        dsimp [le', f']
        by_cases h : s.f (φ a) = x
        · simp [h]
        · have : reach s.f (φ a) (s.f (φ a)) := ⟨1, by
            simp [Function.iterate_one]⟩
          have : s.po.le (φ a) (s.f (φ a))   :=
            (s.order _ _).1 this
          subst hn
          simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, f', le', V', φ]
          obtain ⟨val_1, property_1⟩ := y
          simp_all only [mem_erase, ne_eq, V']
          obtain ⟨left, right⟩ := property_1
          split
          next h_1 => simp_all only [le_refl]
          next h_1 => simp_all only [Subtype.coe_eta]

      have y_le_iter : ∀ k : ℕ, le' y (f'^[k] y) := by
        intro k
        induction k with
        | zero => exact s.po.le_refl (φ y)
        | succ k ih =>
          have : le' (f'^[k] y) (f'^[k + 1] y) :=
          by
            rw [Function.iterate_succ']
            exact step (f'^[k] y)
          exact s.po.le_trans _ _ _ ih this
      have : le' y (f'^[n] y) := y_le_iter n
      rwa [hn] at this


    -- 右⇒左
    have backward : le' y z → reach f' y z := by
      intro hle
      -- 元の世界で reach を取り出す
      have : reach s.f (φ y) (φ z) := (s.order _ _).2 hle
      rcases this with ⟨n, hn⟩

      have φ_iter : ∀ m ≤ n, s.f^[m] (φ y) = φ (f'^[m] y) := by
        intro m hm
        induction m with
        | zero => simp
        | succ m ih =>
          have m_le_n : m ≤ n := Nat.le_of_succ_le hm
          have ih' := ih m_le_n
          rw [Function.iterate_succ', Function.iterate_succ']
          --dsimp [f']
          have not_x : s.f (φ (f'^[m] y)) ≠ x := by
            intro h
            -- s.f^[k] (φ y) が x に到達すると仮定し矛盾を導く
            have stuck_at_x : ∀ k ≥ m + 1, s.f^[k] (φ y) = x := by
              intro k hk
              induction k with
              | zero => simp at hk
              | succ k ihk =>
                if hk' : k ≥ m + 1 then
                  let ihkh := ihk hk'
                  have : s.f x = x := by
                    rw [po_maximal_lem] at pm
                    exact pm
                  rw [Function.iterate_succ']
                  rw [Function.comp_apply]
                  rw [ihkh]
                  exact this
                else
                  have : k = m := by linarith
                  subst this
                  rw [Function.iterate_succ']
                  simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, forall_const, IsEmpty.forall_iff, le_refl,
                    add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, not_false_eq_true, Function.comp_apply, f', le', V', φ]

            have : s.f^[n] (φ y) = x := stuck_at_x n (by linarith)

            rw [hn] at this
            have : (z : α) = x := Subtype.ext_iff.mp this
            have : z.val ∈ V' := z.property
            simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, forall_const, mem_erase, ne_eq,
              not_true_eq_false, and_true, f', le', V', φ]

          rw [Function.comp_apply,Function.comp_apply]  -- m + 1 を展開
          rw [ih']  -- 帰納法の仮定: s.f^[m] (φ y) = φ (f'^[m] y)
          -- 目標: s.f (φ (f'^[m] y)) = φ (f' (f'^[m] y))
          have : φ (f' (f'^[m] y)) = s.f (φ (f'^[m] y)) := by
            dsimp [f']
            have hnot: s.f (φ (f'^[m] y)) ≠ x := not_x
            split_ifs with h
            · simp
              exfalso
              apply hnot
              exact Eq.symm (Subtype.eq (id (Eq.symm h)))
            · rfl
          exact this.symm



      have : f'^[n] y = z := by
        apply Subtype.ext
        suffices φ (f'^[n] y) = φ z from by
          simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, Subtype.mk.injEq, f', le', V', φ]
        let it := φ_iter n (le_refl n)
        rw [←it]
        exact hn

      exact ⟨n, this⟩

    show reach f' y z ↔ y ≤ z
    --これがないと後ろでエラー。
    have po_le_eq_le' : po'.le = le' := by
        dsimp [po']

    simp_all only [ge_iff_le, coe_mem, erase_nonempty, Subtype.coe_eta, f', le', V', φ]
    obtain ⟨val, property⟩ := x
    obtain ⟨val_1, property_1⟩ := y
    obtain ⟨val_2, property_2⟩ := z
    simp_all only [V']
    apply Iff.intro
    · intro a
      simp_all only [forall_const, imp_self]
    · intro a
      simp_all only [imp_self, forall_const]

  -- 全フィールドをまとめて返す
  exact
  { V      := V'
    nonemp := nonemp'
    f      := f'
    po     := po'
    order  := order' }

--- ここから下は全部使われていない。

--setup_poのtraceと、集合族のtraceが同じであること。使ってない？ideals_eq_eraseと内容が同じだが、こちらは連結成分の数が1とは限らない。
private lemma po_trace_ideal (s : Setup_po α) (x : s.V) (pm   : po_maximal s x)
    (geq2 : s.V.card ≥ 2):
  ∀ ss :Finset (s.V.erase x), (po_closuresystem  (po_trace s x pm geq2)).sets (ss.image Subtype.val)
  =  ((po_closuresystem  s).trace x.val x.property geq2).sets (ss.image Subtype.val) :=
by
  intro ss
  -- abbreviations for readability
  let s₀   := s
  let s₁   := po_trace s x pm geq2
  let 𝒞₀   := po_closuresystem s₀
  let 𝒞₁   := po_closuresystem s₁
  let T𝒞₀ := (𝒞₀.trace x.val x.property geq2)

  -- unpack the two `sets` definitions
  dsimp [po_closuresystem, ClosureSystem,
         SetFamily.trace, 𝒞₀, 𝒞₁, T𝒞₀, s₁]

  -- the set appearing on both sides
  set A : Finset α := ss.image Subtype.val with hA

  -- two logical goals coincide; we prove equivalence with `rfl`
  -- because the conditions expand to *identical* formulas:
  --   1. `A ⊆ s.V.erase x`  (comes from `inc_ground`)
  --   2. downward-closure with respect to the *restricted* order,
  --      which is literally the same predicate as in the original
  --      order, just stated on a smaller ground.
  -- All of that is definitionally equal once we unfold `po_trace`.

  change
    (A ⊆ s₁.V ∧
       ∀ v : s₁.V, v.val ∈ A →
         ∀ w : s₁.V, s₁.po.le w v → w.val ∈ A) =
    (_   ∧
     ((_ ∧ _) ∨ (_ ∧ _)))
  -- unpack `s₁.V`
  have hV₁ : s₁.V = s.V.erase x := rfl
  -- «A ⊆ s.V.erase x»  is definitional using `hV₁`
  -- we now prove the two implications to establish equality of props
  apply propext
  constructor
  ------------------------------------------------------------------→
  · intro hL
    rcases hL with ⟨hsub₁, hdown₁⟩
    -- x ∉ A
    have hx_not : x.val ∉ A := by
      intro hx
      have : (x.val) ∈ s.V.erase x := by
        have : (x.val) ∈ s₁.V := hsub₁ hx
        simp [hV₁]
        simp_all only [Finset.mem_image, Subtype.exists, mem_erase, ne_eq, exists_and_right, exists_eq_right,
          Subtype.coe_eta, exists_prop, Subtype.forall, not_false_eq_true, and_self, true_and, and_imp, forall_const,
          not_true_eq_false, coe_mem, and_true, IsEmpty.exists_iff, A, s₁]
      exact (Finset.mem_erase.1 this).1 rfl
    -- A ⊆ s.V
    have hsub₀ : A ⊆ s.V := by
      intro a ha
      have : a ∈ s.V.erase x := by
        have : a ∈ s₁.V := hsub₁ ha
        simpa [hV₁] using this
      exact (Finset.mem_erase.1 this).2
    -- downward‐closed in original order
    have hdown₀ :
        ∀ v : s.V, v.val ∈ A →
          ∀ w : s.V, s.po.le w v → w.val ∈ A := by
      intro v hv w hw
      -- cast to subset of erase (since x ∉ A, the cast succeeds)
      --have hv' : (Subtype.mk v.val ?_) ∈ ss := by
      --  sorry
      -- use restricted downward‐closed
      have hwA : w.val ∈ A := by
  -- hdown₁ は restricted order での downward‐closed 性
        have vin:v.val ∈ s₁.V :=
        by
          simp_all [ s₁]
          obtain ⟨val, property⟩ := x
          obtain ⟨val_1, property_1⟩ := v
          obtain ⟨val_2, property_2⟩ := w
          obtain ⟨w, h⟩ := hv
          simp_all only [not_false_eq_true]
        have win : w.val ∈ s₁.V :=
        by
          simp_all [s₁]
          dsimp [po_maximal] at pm
          by_contra h_contradiction
          specialize pm v
          have h_contra': w = x :=
          by
            simp_all only [A, s₁]
            obtain ⟨val, property⟩ := x
            obtain ⟨val_1, property_1⟩ := v
            subst h_contradiction
            simp_all only [le_refl, Subtype.mk.injEq, forall_const]
          rw [←h_contra'] at pm
          specialize pm hw
          rw [←pm] at vin
          rw [h_contra'] at vin
          contradiction

        have hw': s₁.po.le ⟨w.val,win⟩ ⟨v.val,vin⟩  := by
          exact hw

        --have := hdown₁ ⟨v.val,vin⟩ hv ⟨w.val,win⟩ hw
        --  simp
        specialize hdown₁ ⟨v.val,vin⟩ hv ⟨w.val,win⟩ hw'
        exact hdown₁

      simp_all only [Finset.mem_image, Subtype.exists, mem_erase, ne_eq, exists_and_right, exists_eq_right,
        Subtype.coe_eta, exists_prop, Subtype.forall, not_false_eq_true, and_self, true_and, and_imp, forall_const,
        not_true_eq_false, coe_mem, and_true, IsEmpty.exists_iff, A, s₁]

    -- choose left branch of the big disjunction
    exact And.intro hx_not (Or.inl ⟨hsub₀, hdown₀⟩)
  ------------------------------------------------------------------←
  · intro hR
    rcases hR with ⟨hx_not, hcase⟩
    -- A ⊆ s₁.V  (because x ∉ A and A ⊆ s.V)
    have hsub₁ : A ⊆ s₁.V := by
      intro a ha
      cases hcase with
      | inl hideal =>
        have : a ∈ s.V := hideal.1 ha
        have ax : a ≠ x.val := by
          intro hax; subst hax; exact hx_not ha
        have : a ∈ s.V.erase x := Finset.mem_erase.mpr ⟨ax, this⟩
        simpa [hV₁]
      | inr hideal =>
        obtain ⟨hideal1, hideal⟩ := hideal
        have : a ∈ s.V := by
          have :A ⊆ s.V := by exact union_subset_left hideal1
          exact this ha
        have ax : a ≠ x.val := by
          intro hax; subst hax; exact hx_not ha
        have : a ∈ s.V.erase x := Finset.mem_erase.mpr ⟨ax, this⟩
        simpa [hV₁]
    -- downward‐closed for restricted order
    have hdown₁ :
        ∀ v : s₁.V, v.val ∈ A →
          ∀ w : s₁.V, s₁.po.le w v → w.val ∈ A :=
    by
      intro v hv w hw
      -- translate to original order
      have hv₀ : v.val ∈ A := hv
      have hw₀ :
        s.po.le ⟨w.val, ?_⟩ ⟨v.val, ?_⟩ :=
      by
        exact hw
      cases hcase with
      | inl hideal =>
        have vin : v.val ∈ s.V := by
          exact mem_of_mem_erase (hsub₁ hv)
        have : w.val ∈ A := hideal.2 ⟨v.val, ?_⟩ hv₀ ⟨w.val, ?_⟩ hw₀

        · exact this
        · exact mem_of_mem_erase (hsub₁ hv)
        · let hw := w.property
          dsimp [s₁] at hw
          dsimp [po_trace] at hw
          rw [Finset.mem_erase] at hw
          exact hw.2


      | inr hideal =>
        -- A ⊆ A ∪ {x} で閉じている方を使う
        obtain ⟨hideal1, hideal⟩ := hideal
        have vin: v.val ∈ s.V := by
          dsimp [s₁] at hsub₁
          dsimp [po_trace] at hsub₁
          rw [Finset.subset_erase] at hsub₁
          exact hsub₁.1 hv₀

        let hw2 := w.property
        dsimp [s₁] at hw2
        dsimp [po_trace] at hw2
        rw [Finset.mem_erase] at hw2
        have win: w.val ∈ s.V := by
          exact hw2.2

        have win2: w.val ∈ (A ∪ {x.val}) :=
        by
          specialize hideal ⟨v.val,vin⟩

          have :v.val ∈ A ∪ {↑x} := by
            exact Finset.mem_union_left _ hv₀
          simp at hideal
          have :↑v ∈ A ∨ v.val = x.val := by
            rw [Finset.mem_union] at this
            cases this with
            | inl hA => exact Or.intro_left (v.val = x.val) hv
            | inr hx => exact Or.intro_left (v.val = x.val) hv

          specialize hideal this

          specialize hideal w.val  win

          have : s.po.le ⟨↑w, win⟩ ⟨↑v, vin⟩ :=
          by
            --hw₀ : ⟨↑w, ⋯⟩ ≤ ⟨↑v, ⋯⟩
            --hw : w ≤ v
            exact hw

          specialize hideal this
          simp
          exact hideal
        rw [Finset.mem_union] at win2
        cases win2 with
        | inl hA => exact hA
        | inr hx =>
          -- x ∉ A, contradiction
          simp at hx
          rw [hx] at hw2
          exfalso
          let hw1 := hw2.1
          contradiction

    exact And.symm ⟨hdown₁, hsub₁⟩

--使われてない。
private lemma downward_closed_of_restrict
    {β : Type}
    {le : β → β → Prop}
    {A : Finset β}
    (hdown : ∀ v, v ∈ A →
            ∀ w, le w v → w ∈ A) :
    ∀ v, v ∈ (A : Finset β) →
      ∀ w, le w v → w ∈ A := hdown
