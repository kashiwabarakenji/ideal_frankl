--IdealSum.leanをChatGPTにリファクタリングしてもらって作った補題のつもりだったけど、途中で方向性が変わって、sum_bijの実験。
--基本的に、全単射の対応としては、subtypeのBijectionを用いた。でも単射性、全射性はsubtypeでない証明を求められた。
--それで、subtypeのBijectiveの条件から、subtypeでない単射性、全射性を証明する関数を作った。
--だいたいできたけど、heartbeatsが足りないのか、エラーが出る。よって実用性がない。
--いまのところ、subtypeを用いないものidealSumなどを用いた方がよい。
--surjのマッチがうまくいかない。surj_to_sum_bij_format_refac5の証明がうまくいかない。
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
set_option maxHeartbeats 40000000
--set_option diagnostics true

namespace Mathematics

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

/- テストコード　　消して良い。
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
-/

def domain00 (F : SetFamily α) (v : α) [DecidablePred F.sets] : Finset (Finset α) :=
  (Finset.powerset F.ground).filter (λ s => F.sets s ∧ v ∈ s)

def range00 (F : SetFamily α) (v : α) [DecidablePred F.sets] :  Finset (Finset α) :=
  (Finset.powerset (F.ground.erase v)).filter (λ s => ∃ H, F.sets H ∧ v ∈ H ∧ s = H.erase v)

--subtypeではないほう。
def f_wrapped (F : SetFamily α) (v : α) [DecidablePred F.sets]
  (s : Finset α) (_ : s ∈ domain00 F v) : Finset α :=
  s.erase v

def f_wrapped_if (F : SetFamily α) (v : α) [DecidablePred F.sets]
  (s : Finset α): Finset α :=
  if  s ∈ domain00 F v  then s.erase v else s

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
        obtain ⟨_, _, hs13⟩ := hs₁
        obtain ⟨_, _, hs23⟩ := hs₂
        exact Mathematics.set_eq_of_erase_eq hs13 hs23 h
  rename_i inst inst_1 _ inst_3
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



def inj (F : SetFamily α) (x : α) (hx : x ∈ F.ground) :=
  (bijective_map_erase_x F x hx).left

lemma inj_to_sum_bij_format (F : SetFamily α) (x : α) (hx : x ∈ F.ground) :
  ∀ (a₁ : { S // S ∈ domain00 F x }) (_ : a₁.val ∈ domain00 F x),
    ∀ (a₂ : { S // S ∈ domain00 F x }) (_ : a₂.val ∈ domain00 F x),
      (f F x a₁).val = (f F x a₂).val → a₁ = a₂ :=
  λ _ _ _ _ h =>
    inj F x hx (Subtype.ext h)

def surj (F : SetFamily α) (x : α) (hx : x ∈ F.ground) :=
  (bijective_map_erase_x F x hx).right

lemma surj_to_sum_bij_format_refac5 (F : SetFamily α) (x : α) (hx : x ∈ F.ground) :
  ∀ b : Finset α, b ∈ range00 F x → ∃ a : {a // a ∈ domain00 F x}, (a).val.erase x = b :=
by
  intros b hb
  obtain ⟨⟨a, ha⟩, ha2⟩ := surj F x hx ⟨b, hb⟩ -- Use subtype explicitly here
  use ⟨a, ha⟩
  --rw [f_wrapped]
  simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, Finset.erase_eq_of_not_mem]
  dsimp [f] at ha2
  simp only [Subtype.mk.injEq] at ha2
  exact ha2

lemma surj_to_sum_bij_format_refac4 (F : SetFamily α) (x : α) (hx : x ∈ F.ground) :
  ∀ b : Finset α, b ∈ range00 F x → ∃ a : Finset α, ∃ ha : a ∈ domain00 F x, (f_wrapped F x a ha).erase x = b :=
by
  intros b hb
  obtain ⟨⟨a, ha⟩, ha2⟩ := surj F x hx ⟨b, hb⟩ -- `subtype` を用いていることを明示
  use a
  use ha
  rw [f_wrapped]
  simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, Finset.erase_eq_of_not_mem]
  dsimp [f] at ha2
  simp only [Subtype.mk.injEq] at ha2
  exact ha2

--goalのほうに合わせると、rangeがsubtypeでなく、domianがsubtypeになっている。
-- Bijective.2の条件を使った証明が本来の意図のはず。
lemma surj_to_sum_bij_format_refac3 (F : SetFamily α) (x : α) (hx : x ∈ F.ground) :
  ∀ b : Finset α, b ∈ range00 F x → ∃ a : {a // a ∈ domain00 F x}, (f_wrapped F x a.val a.property).erase x = b :=
by
  intros b hb
  obtain ⟨a, ha1, ha2⟩ := surj F x hx ⟨b, hb⟩
  use a -- `subtype` を用いて `a` を包む
  rw [f_wrapped]
  rename_i inst inst_1 _
  simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, Finset.erase_eq_of_not_mem]


--suj(Surjective)の条件をsum_bijのsurjectiveに書き換える関数
--surjectiveのゴール ∀ b ∈ range00 F x, ∃ a, ∃ (_ : a ∈ ?m.35483), (↑a).erase x = b
--これを証明する必要。 ∃ a, ∃ (ha : a ∈ domain00 F x)この書き方がポイントだった。ゴールから逆算して補題を作る。

lemma surj_to_sum_bij_format_step1 (F : SetFamily α) (x : α) (hx : x ∈ F.ground) (b : Finset α) (hb : b ∈ range00 F x) :
  ∃ (a : { S // S ∈ domain00 F x }), (f F x a) = ⟨b, hb⟩ :=
  let ⟨a, ha1⟩ := surj F x hx ⟨b, hb⟩
  ⟨a, ha1⟩

-- 仮定: `f_wrapped` は `Finset α` を返す関数である
lemma f_wrapped_erase_eq (F : SetFamily α) (x : α) (a : Finset α) (ha : a ∈ domain00 F x) :
  (f_wrapped F x a ha).erase x = (f F x ⟨a, ha⟩).val.erase x :=
  by
    -- `f_wrapped` の定義と `f` の結果が一致することを証明
    -- この部分は具体的な `f_wrapped` の定義に依存します
    -- 以下は仮定した形に基づく証明の例です
    rw [f_wrapped, f]
    -- ここで、`erase` の操作が両辺に適用されることを確認



--refact2から頑張ってsimp_allを取り除いた。
--以下はlemmaに分けるほどでもなかった。
lemma finset_val_erase_eq_self (F : SetFamily α) (x : α) (asub : { S // S ∈ domain00 F x })  :
  (f F x asub).val = ((f F x asub).val.erase x) :=
  by
    have nx: x ∉ (f F x asub).val := by
      dsimp [f]
      simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true] --全部必要。
    rw [Finset.erase_eq_of_not_mem nx]

lemma surj_to_sum_bij_format_refac2 (F : SetFamily α) (x : α) (hx : x ∈ F.ground) :
  ∀ b : Finset α, b ∈ range00 F x → ∃ (a : Finset α) (ha : a ∈ domain00 F x), (f_wrapped F x a ha).erase x = b :=
  by
    intro b hb
    -- `surj F x hx ⟨b, hb⟩` の結果から `a` と `ha1` を取り出す
    let ⟨asub, ha1⟩ := surj F x hx ⟨b, hb⟩
    -- `f_eq_b` を導出
    have f_eq_b: (f F x asub).val = b := by
      simp only [Subtype.coe_eta] at ha1
      rw [ha1]
      --theorem Subtype.coe_eta {α : Sort u_1}  {p : α → Prop}  (a : { a // p a }) (h : p ↑a) : { val := ↑a, property := h } = a

    -- `finset_val_erase_eq_self` を使用
    have subs := finset_val_erase_eq_self F x asub

    exists asub.val
    exists asub.property
    -- `erase_eq_of_mem_range00` を使って証明を完了
    rw [subs] at f_eq_b
    rw [f_wrapped_erase_eq F x asub asub.property]
    -- `ha1` を使用して証明を完了
    exact f_eq_b

    --exact erase_eq_of_mem_range00 F x asub.property f_eq_b

--以下はlemmaに分けるほどでもなかった。
lemma erase_eq_of_mem_range00 (F : SetFamily α) (x : α)(ha:a ∈ domain00 F x) (ha1 : (f F x ⟨a, ha⟩).val.erase x = b) :
  (f_wrapped F x a ha).erase x = b :=
  by
--    -- `f_wrapped` の定義と `f` の結果が一致することを証明
    rw [f_wrapped_erase_eq F x a ha]
    -- `ha1` を使用して証明を完了
    exact ha1


lemma surj_to_sum_bij_format_refac1 (F : SetFamily α) (x : α) (hx : x ∈ F.ground) :
  ∀ b : Finset α, b ∈ range00 F x → ∃ (a : Finset α) (ha : a ∈ domain00 F x), (f_wrapped F x a ha).erase x = b :=
  by
    intro b hb
    -- `surj F x hx ⟨b, hb⟩` の結果から `a` と `ha1` を取り出す
    --#check surj F x hx ⟨b, hb⟩
    --surj F x hx ⟨b, hb⟩ : ∃ a, (fun s ↦ f F x s) a = ⟨b, hb⟩
    let ⟨asub, ha1⟩ := surj F x hx ⟨b, hb⟩
    --#check asub --asub : { S // S ∈ domain00 F x }
    --#check ha1 -- (fun s ↦ f F x s) asub = ⟨b, hb⟩
    --#check (f F x asub).val
    have f_eq_b: (f F x asub).val = b := by
      simp_all only [Subtype.coe_eta]
    -- `a` とその証明を `exists` で使用
    have subs: (f F x asub).val = ((f F x asub).val.erase x) := by
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true,
      Finset.erase_eq_of_not_mem, Finset.coe_mem, exists_const]
      rename_i inst inst_1 _
      ext
      simp_all only [Finset.mem_erase, ne_eq, iff_and_self]
      intro a a_1
      subst a_1
      injection ha1
      rename_i a_1 val_eq
      subst val_eq
      simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and]

    exists asub.val
    exists asub.property
    -- `erase_eq_of_mem_range00` を使って証明を完了
    rw [subs] at f_eq_b
    exact erase_eq_of_mem_range00 F x asub.property f_eq_b

/- うごいてない。消す。
lemma surj_to_sum_bij_format_refac0 (F : SetFamily α) (x : α) (hx : x ∈ F.ground):
  ∀ b : Finset α, b ∈ range00 F x → ∃ (a : Finset α) (ha : a ∈ domain00 F x), (f_wrapped F x a ha).erase x = b :=
  by
    intro b hb
    -- `surj F x hx ⟨b, hb⟩` の結果から `a` と `ha1` を取り出す
    let ⟨a, ha1⟩ := surj F x hx ⟨b, hb⟩
    -- `a` とその証明を `exists` で使用
    exists a.val
    exists a.property
    -- `f_wrapped_erase_eq` を用いて `f_wrapped` の結果を置き換える
    rw [f_wrapped_erase_eq F x a.val a.property]
    -- 最後に `ha1` を使って証明を完了
    exact erase_eq_of_mem_range00 F x hx ha ha1 --haは仮定になっていない。
  -/



lemma surj_to_sum_bij_format_refac (F : SetFamily α) (x : α) (hx : x ∈ F.ground) :
  (∀ b : Finset α, b ∈ range00 F x → ∃ (a : Finset α) (ha : a ∈ domain00 F x), (f_wrapped F x a ha).erase x = b) :=
  by
    intro b hb
    let ⟨a, ha1⟩ := surj F x hx ⟨b, hb⟩
    exists a
    dsimp [f_wrapped]
    --goal (f_wrapped F x ↑a ⋯).erase x = b   ∃ (_ : ↑a ∈ domain00 F x), ((↑a).erase x).erase x = b
    --(fun s ↦ f F x s) a = ⟨b, hb⟩
    rename_i inst inst_1 _
    simp_all only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true,
      Finset.erase_eq_of_not_mem, Finset.coe_mem, exists_const]
    obtain ⟨val, property⟩ := a
    simp_all only
    symm
    rw [Subtype.ext_iff] at ha1
    simp_all only
    subst ha1
    simp_all only [Finset.coe_mem]
    apply Eq.refl


lemma surj_to_sum_bij_format (F : SetFamily α) (x : α) (hx : x ∈ F.ground) :
  ∀ b, b ∈ range00 F x → ∃ a, ∃ (ha : a ∈ domain00 F x), (f_wrapped F x a ha).erase x = b :=
  λ b hb =>
  let ⟨a, ha⟩ := surj F x hx ⟨b, hb⟩
  ⟨a.val, a.property, by
    -- `ha` は `(f F x a).val = b` の証明
    have h : (f F x ⟨a, a.property⟩).val = b := by
      simp_all only [Subtype.coe_eta]
    -- `f F x ⟨a, _⟩.val.erase x = b` を示す
    rw [← h]
    -- `b` が `range00 F x` に属するので、`b.erase x` が `f F x ⟨a, _⟩.val.erase x` と一致する
    simp only [Function.funext_iff, Finset.mem_erase] at h
    subst h
    obtain ⟨val, property⟩ := a
    simp only [f_wrapped]
    simp_all only [↓reduceIte, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true,
      Finset.erase_eq_of_not_mem]
    apply Eq.refl
  ⟩

/-
lemma surj_to_sum_bij_format2(F : SetFamily α) (x : α) (hx : x ∈ F.ground) :
  ∀ b, b ∈ range00 F x → ∃ a, ∃ (ha : a ∈ domain00 F x), (f_wrapped F x a ha).erase x = b :=
  λ b hb =>
  let ⟨a, ha⟩ := surj F x hx ⟨b, hb⟩
  ⟨a.val, a.property, by
    -- `ha` は `(f F x a).val = b` の証明
    have h : (f F x ⟨a, a.property⟩).val = b := by
      simp_all only [Subtype.coe_eta]
    -- `f F x ⟨a, _⟩.val.erase x = b` を示す
    rw [← h]
    -- `b` が `range00 F x` に属するので、`b.erase x` が `f F x ⟨a, _⟩.val.erase x` と一致する
    simp only [Function.funext_iff, Finset.mem_erase] at h
    subst h
    obtain ⟨val, property⟩ := a
    simp only [f_wrapped]
    simp_all only [ Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true,
      Finset.erase_eq_of_not_mem]
    apply Eq.refl
  ⟩
  -/

/- subtype版。動くがつかってないのでコメントアウト。
lemma surj_to_sum_bij_format_sub (F : SetFamily α) (x : α) (hx : x ∈ F.ground) :
  ∀ (b : { T // T ∈ range00 F x }),-- (hb : b.val ∈ range00 F x),
    ∃ (a : { S // S ∈ domain00 F x }) ,--(ha : a.val ∈ domain00 F x),
      (f F x a).val = b.val := --λ b => let ⟨a, ha⟩ := surj F x hx b; ⟨⟨a, a.property⟩, ha⟩
   --#check Subtype.ext_iff_val.mpr
   λ b =>
    let ⟨a, ha⟩ := surj F x hx b
  ⟨⟨a, a.property⟩, by
    -- subtype の等価性を示す
    rename_i inst inst_1 _
    subst ha
    simp_all only [Subtype.coe_eta]
  ⟩

--subtypeじゃない版。微妙にガールにマッチしなかったので消して良い。
lemma surj_to_sum_bij_format_if (F : SetFamily α) (x : α) (hx : x ∈ F.ground) :
  let adom:= domain00 F x
  ∀ b, b ∈ range00 F x → ∃ a, a ∈ adom ∧
  (f_wrapped_if F x a).erase x = b :=
  λ b hb =>
  let ⟨a, ha⟩ := surj F x hx ⟨b, hb⟩
  ⟨a.val, a.property, by
    -- `ha` は `(f F x a).val = b` の証明
    have h : (f F x ⟨a, a.property⟩).val = b := by
      rename_i inst inst_1 _
      simp_all only [Subtype.coe_eta]
    -- `f F x ⟨a, _⟩.val.erase x = b` を示す
    rw [← h]
    -- `b` が `range00 F x` に属するので、`b.erase x` が `f F x ⟨a, _⟩.val.erase x` と一致する
    simp only [Function.funext_iff, Finset.mem_erase] at h
    rename_i inst inst_1 _
    subst h
    simp_all only [Subtype.coe_eta]
    simp_all only [Subtype.coe_eta, Finset.coe_mem]
    obtain ⟨val, property⟩ := a
    simp_all only
    dsimp [domain00, range00]
    simp only [f_wrapped_if]
    simp_all only [↓reduceIte, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true,
      Finset.erase_eq_of_not_mem]
    apply Eq.refl

  ⟩
-/

lemma conv (F : SetFamily α) [DecidablePred F.sets] (x : α)
  (s : ∀ b : Finset α, b ∈ range00 F x → ∃ a : {a // a ∈ domain00 F x}, a.val.erase x = b) :
  ∀ (bb : Finset α), bb ∈ range00 F x → ∃ (a : Finset α), ∃ (_ : a ∈ domain00 F x), a.erase x = bb :=
λ bb hbb =>
  let ⟨a, ha⟩ := s bb hbb
  ⟨a.val, a.property, ha⟩

def g_pub (F : SetFamily α) (x : α) (s: {S // S ∈ domain00 F x}) : ℕ := Finset.card (s.val)
def h_pub (F : SetFamily α) (x : α)  (s: {S // S ∈ (range00 F x)}) : ℕ := (Finset.card s.val) + 1

lemma sum_bijection (F : SetFamily α) [DecidablePred F.sets] (x : α) (hx : x ∈ F.ground) :
  (domain00 F x).sum Finset.card = (range00 F x).sum Finset.card + (range00 F x).card := by
  --apply @Finset.sum_bij _ _ _ _  _ _ ({S // S ∈ (domain00 F x)}) ({T // T ∈ (range00 F x)})
  -- (g_pub F x)
   --(g_pub: {S // S ∈ domain00 F x}  → Nat) --Finset.card s.val)
  -- (h_pub F x)--: {T // T ∈ range00 F x}  → Nat) --(Finset.card t.val) + 1)
  -- goal (domain00 F x).sum Finset.card = (range00 F x).sum Finset.card + (range00 F x).card

  let surj1 := surj_to_sum_bij_format_refac F x hx
  simp at surj1
  dsimp [f_wrapped] at surj1
  simp at surj1
  #check surj1
  --let surj0 : (∀ b ∈ range00 F x, ∃ a : {a // a ∈ domain00 F x}, (a).val.erase x = b) := surj_to_sum_bij_format_refac5 F x hx
  --dsimp [f_wrapped] at surj0
  #check Finset.sum_bij
   (f F x)
   (by
      intros s hs
      exact f_mem_range00_sub F x s
   )

   -- 単射性の証明 --なぜかsubtypeでない方の証明が必要になる。
   (inj_to_sum_bij_format F x hx)
   -- 全射性の証明　--なぜかsubtypeでない方の証明が必要になる。
   (by
    simp
    exact surj1)
   --(surj_to_sum_bij_format_refac2 F x hx)
   -- 最後の等式の証明
   (by
      tauto
   )
   --gとhの可換性の証明
   (by
     intro (ss : {S // S ∈ domain00 F x})

     have hl: ∀ (s: {S // S ∈ domain00 F x}), (g_pub F x) s = (h_pub F x) (f F x s) := by
       intro s
       simp [g, h, f]
       rw [f_wrapped]
       exact Finset.card_erase_of_mem x

     exact hl ss
   )
