--ChatGPTにリファクタリングしてもらって作った補題。
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Data.Subtype
import Mathlib.Tactic
import Mathematics.BasicDefinitions
import Mathematics.BasicLemmas
import LeanCopilot

namespace Mathematics

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

--subtypeからvalを取り出すのにcasesを用いた例
lemma subtype_eq_implies_val_eq {α : Type*} {P : α → Prop} (a b : Subtype P) (h : a = b) : a.val = b.val :=
by
  cases h -- これにより、`a = b` が `a.val = b.val` に変換される
  rfl    -- 同じものであることを示す

def even_nat_pair := { p : ℕ × ℕ // p.1 % 2 = 0 ∧ p.2 % 2 = 0 }

def g (p : even_nat_pair) : even_nat_pair := ⟨(p.val.1 + 2, p.val.2 + 2),
  (by
    obtain ⟨h1, h2⟩ := p.property
    rw [Nat.add_mod, h1, zero_add, Nat.mod_self]
    rw [Nat.add_mod, h2, zero_add, Nat.mod_self]
    simp
  )
⟩

--subtypeで定義された関数gのinjectiveを証明する。subtype間の関数でも頑張れば単射性は証明できる。
lemma g_injective : Function.Injective g := by
  intros p1 p2 h
  --h : g p1 = g p2
  injection h with val_eq_1
  --val_eq_1 : (↑p1).1 = (↑p2).1 ∧ (↑p1).2 = (↑p2).2
  simp_all only [Prod.mk.injEq, add_left_inj]
  --obtain ⟨left, right⟩ := val_eq_1
  cases p1 ; rename_i val property --p1は分解しているのにp2は分解しないのはなぜ。
  --goal ⟨val, property⟩ = p2
  --goal ⟨(fst, snd), property⟩ = p2
  obtain ⟨fst, snd⟩ := val  -- これがないと証明が通らない
  obtain ⟨left_1, right_1⟩ := property
  simp_all only [Prod.mk.eta, Subtype.coe_eta]
  --theorem Subtype.coe_eta {α : Sort u_1}  {p : α → Prop}  (a : { a // p a }) (h : p ↑a) :{ val := ↑a, property := h } = a

/-
lemma test_set_eq (F : SetFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) :
  let filteredSetWithX := (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)
  let filteredSetWithoutX := (Finset.powerset (F.ground.erase x)).filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x)
  Function.Injective (λ (s : filteredSetWithX) => s.val.erase x) :=
by
  rw [Function.Injective]
  intros s₁ hs₁ s₂ hs₂ h
  dsimp [filteredSetWithoutX ] at hs₁ hs₂



  simp only [Finset.mem_filter, Finset.mem_powerset] at hs₁ hs₂
  obtain ⟨hs11, hs12, hs13, hs14, hs15⟩ := hs₁
        obtain ⟨hs21, hs22, hs23, hs24, hs25⟩ := hs₂
        have h1: x ∈ s₁ ∪ {x} := by simp_all
        have h2: x ∈ s₂ ∪ {x} := by simp_all

        have hn1: x ∉ s₁ := by
          intro hn1n
          rw [hs15] at hn1n
          rw [Finset.mem_union, Finset.mem_singleton] at h2
          simp at h2
          rename_i inst inst_1 inst_2 inst_3
          subst hs25 hs15
          simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true]

        have hn2: x ∉ s₂ := by
          intro hn2n
          rw [hs25] at hn2n
          rw [Finset.mem_union, Finset.mem_singleton] at h1
          simp at h1
          rename_i inst inst_1 inst_2 inst_3
          subst hs25 hs15
          simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, and_true]

        simp at h

        #check Mathematics.set_eq_of_erase_eq hn1 hn2 h
        #check @Mathematics.set_eq_of_erase_eq  s₁ s₂ x hn1 hn2 h
-/

def domain00 (F : SetFamily α) (v : α) [DecidablePred F.sets] : Finset (Finset α) :=
  (Finset.powerset F.ground).filter (λ s => F.sets s ∧ v ∈ s)

def range00 (F : SetFamily α) (v : α) [DecidablePred F.sets] :  Finset (Finset α) :=
  (Finset.powerset (F.ground.erase v)).filter (λ s => ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v)

--subtypeではないほう。
def f_wrapped (F : SetFamily α) (v : α) [DecidablePred F.sets]
  (s : Finset α) (_ : s ∈ domain00 F v) : Finset α :=
  s.erase v

-- s.val.erase v が range00 に属することを示す補題 subtype版
lemma f_mem_range00_sub (F : SetFamily α) (v : α) [DecidablePred F.sets]
  (s : { S // S ∈ domain00 F v }) : (s.val.erase v) ∈ (range00 F v) :=
by
  simp [range00]
  rename_i inst inst_1 _ inst_3
  simp_all only [domain00]
  obtain ⟨val, property⟩ := s
  simp [domain00] at property
  obtain ⟨left, right⟩ := property
  obtain ⟨left_1, right⟩ := right
  apply And.intro
  · intro y hy
    simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
    obtain ⟨_, right_1⟩ := hy
    exact left right_1
  · apply Exists.intro
    · apply And.intro
      on_goal 2 => {
        apply And.intro
        on_goal 2 => {apply Eq.refl
        }
        · simp_all only
      }
      · simp_all only

--subtypeでないほうなので、今回は使わない。
lemma f_mem_range00 (F : SetFamily α) (v : α) [DecidablePred F.sets]
  (s : Finset α) (hs : s ∈ domain00 F v) : s.erase v ∈ range00 F v := by
  simp [range00]
  simp_all only [domain00]
  simp [domain00] at hs
  obtain ⟨left, right⟩ := hs
  obtain ⟨left_1, right⟩ := right
  apply And.intro
  · intro y hy
    simp_all only [Finset.mem_erase, ne_eq, not_false_eq_true, true_and]
    obtain ⟨_, right_1⟩ := hy
    exact left right_1
  · apply Exists.intro
    · apply And.intro
      on_goal 2 => {
        apply And.intro
        on_goal 2 => {apply Eq.refl}
        · simp_all only
      }
      · simp_all only

--subtypeからsubtypeへの関数
def f (F : SetFamily α) (v : α) [DecidablePred F.sets] (s : { S // S ∈ domain00 F v }) : { S // S ∈ range00 F v } := ⟨s.val.erase v, f_mem_range00_sub F v s⟩

--大きな集合とvを除いた小さな集合の間の全単射fの証明。ただ、今から思えば、Bijectiveを経由しないで全射性、単射性を直接熱かった方がよいかも。
lemma bijective_map_erase_x (F : SetFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) :
  Function.Bijective (λ s => f F x s ):= --subtypeを使ったバージョンになっている。
  -- ここで関数の定義域と終域が集合になっているのでdomainとrangeがsubtypeになってしまっている。subtypeだとうまくいかない。
by
  constructor --単射と全射を証明する。

  -- 単射性の証明
  rw [Function.Injective]
  intros s₁_sub s₂_sub ha_sub
  injection ha_sub with h1
  have inj:  ∀ (a₁ : Finset α) (ha₁ : a₁ ∈ (domain00 F x)) (a₂ : Finset α) (ha₂ : a₂ ∈ (domain00 F x)),
    (f_wrapped F x a₁ ha₁) = (f_wrapped F x a₂ ha₂) → a₁ = a₂ :=
       by

        intros s₁ hs₁ s₂ hs₂ h
        -- h (fun s x_1 ↦ s.erase x) s₁ hs₁ = (fun s x_1 ↦ s.erase x) s₂ hs₂
        dsimp [domain00] at hs₁ hs₂
        simp only [Finset.mem_filter, Finset.mem_powerset] at hs₁ hs₂
        dsimp [f_wrapped] at h
        obtain ⟨hs11, hs12, hs13⟩ := hs₁
        obtain ⟨hs21, hs22, hs23⟩ := hs₂
        exact Mathematics.set_eq_of_erase_eq hs13 hs23 h
  rename_i inst inst_1 inst_2 inst_3
  obtain ⟨val, property⟩ := s₁_sub
  obtain ⟨val_1, property_1⟩ := s₂_sub
  simp_all only [Subtype.mk.injEq]
  apply inj
  · exact h1
  · simp_all only
  · simp_all only

  -- 全射性の証明
  rw [Function.Surjective]
  intro b
  let bcopy := b
  have bcopyhave: bcopy = b := by
    exact rfl

  have ⟨bval, bpro⟩ := b
  have b_eq: bval = bcopy.val := by
    simp_all only [bcopy]

  rw [range00] at bpro

  rw [Finset.mem_filter, Finset.mem_powerset] at bpro
  obtain ⟨gsub, H, H_set, H_mem, H_eq⟩ := bpro
  -- goal ∃ a, f F x a = b  aはsubtypeなので注意。
  let gcopy := gsub
  rw [H_eq] at gcopy
  have gsub': H ⊆ F.ground := by
    exact Mathematics.subset_of_erase_subset H_mem hx gcopy
  --lemma subset_of_erase_subset {A B : Finset α} [DecidableEq α] {x : α} (hxA : x ∈ A) (hxB : x ∈ B) (h : A.erase x ⊆ B.erase x) : A ⊆ B

  have H_in_domain : H ∈ domain00 F x := by
    simp only [domain00, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨gsub', H_set, H_mem⟩

  have val_eq : (f F x ⟨H, H_in_domain⟩).val = bval := by
    simp [f, f_wrapped]
    rw [H_eq]

  use ⟨H, H_in_domain⟩
  apply Subtype.ext
  rw [Subtype.coe_mk]
  rw [val_eq]

--#check Finset.sum_bij

lemma sum_bijection (F : SetFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) :
  (domain00 F x).sum Finset.card = (range00 F x).sum Finset.card + (range00 F x).card :=
by
  apply Finset.sum_bij (λ (s: domain00 F x) => ((f F x s),f_mem_range00_sub F x s) -- 写像の定義と終域に属することの証明

  · --goal
    intro s hs
    fun g : (s: domain00 F v) → ℕ
    fun h : (s:range00 F v) → ℕ



  -- 単射性の証明
  {
    intros a₁ ha₁ a₂ ha₂ h
    exact Finset.erase_eq_iff_of_mem ha₁ ha₂ hx h
  }
  -- 全射性の証明
  {
    intros s hs
    obtain ⟨H, hH1, hH2, hH3⟩ := hs
    use s ∪ {x}
    simp [H, hH1, hH2, hH3]
  }
  -- 最後の等式の証明
  {
    intros a ha
    rw [Finset.card_erase_of_mem hx]
    simp
  }

lemma sumbij (F : SetFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) :
  let filteredSetWithX := (Finset.powerset F.ground).filter (λ s => F.sets s ∧ x ∈ s)
  let filteredSetWithoutX := (Finset.powerset (F.ground.erase x)).filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x)
  filteredSetWithX.sum Finset.card = filteredSetWithoutX.sum Finset.card + filteredSetWithoutX.card :=
by
  exact sum_bijection F x hx



lemma sum_of_ff_plus_card_eq_sum (F : SetFamily α) (x : α) (hx : x ∈ F.ground)
  (gcard: F.ground.card ≥ 2) :
  ∀ (filteredSetWithX filteredSetWithoutX : Finset (Finset α)),
  filteredSetWithX = Finset.filter (λ s => F.sets s ∧ x ∈ s) F.ground.powerset →
  filteredSetWithoutX = Finset.filter (λ s => ∃ H, F.sets H ∧ x ∈ H ∧ s = H.erase x) (F.ground.erase x).powerset →
  filteredSetWithX.sum (λ s => s.card - 1) + filteredSetWithoutX.card = filteredSetWithoutX.sum Finset.card :=
by
  intros filteredSetWithX filteredSetWithoutX hWithX hWithoutX
  have large_sum_eq_small_sum_plus_small_card :
    filteredSetWithX.sum Finset.card = filteredSetWithoutX.sum Finset.card + filteredSetWithoutX.card :=
    by
      rw [hWithX, hWithoutX]
      exact sumbij F x hx

  have positive: ∀ s ∈ filteredSetWithX, s.card ≥ 1 := by
    intros s hs
    simp only [Finset.mem_filter] at hs
    obtain ⟨_, h_in_set⟩ := hs
    exact Finset.one_le_card_iff.2 ⟨x, h_in_set.2⟩

  have sub_eq: filteredSetWithX.sum (λ s => s.card - 1) =
    filteredSetWithX.sum Finset.card - filteredSetWithX.card := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Nat.smul_one_eq_mul, mul_one]
    refl

  rw [sub_eq, large_sum_eq_small_sum_plus_small_card]
  rw [Nat.add_sub_assoc (Finset.card_le_of_sum_le filteredSetWithX positive)]
  rfl
