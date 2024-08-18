import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Mathlib.Init.Function
import Mathlib.Init.Logic
import Mathematics.BasicDefinitions
import Mathematics.BasicLemmas
import Mathematics.IdealTrace
import LeanCopilot

variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

namespace Mathematics

def hasDegreeOneSetFamily (F : SetFamily α) : Prop :=
  ∃ (v : α), degree F v = 1

--次数が1の点をtraceをすると標準化次数和が下がること。
theorem trace_does_not_decrease_normalized_degree_sum {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2) (deg1: degree F x = 1) :
  (normalized_degree_sum (IdealTrace.trace F x hx gcard)) ≥ normalized_degree_sum F :=
  by
    sorry

--補題をノーヒントで自動で出してもらったがろくなものがないかも。人間があらすじを書いて補題を作ってもらう必要がある。

--xでtraceするとその集合族にはxが含まれないこと。別のところで証明されている可能性あり。
lemma trace_sets_property {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2) :
  ∀ (s :Finset α ),(IdealTrace.trace F x hx gcard).sets s → x ∉ s :=
  by
    sorry

--degreeの定義を書き写しただけか。簡単に証明できたので証明しておいた。使わないかも。
lemma degree_calculation {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x : α) :
  degree F x = (Finset.filter (λ s => F.sets s ∧ x ∈ s) (all_subsets F.ground)).card :=
  by
    simp_all only [degree, all_subsets, Finset.card_filter]
    simp [Finset.filter]

-- normalized_degree_sumの定義を書き写しただけか。/の記法は割り算？これは間違っているかも。
lemma normalized_degree_sum_calculation {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) :
  normalized_degree_sum F = (Finset.sum ((all_subsets F.ground).filter F.sets) (λ s => s.card)) / F.ground.card :=
  by
    simp_all only [normalized_degree_sum, total_size_of_hyperedges, number_of_hyperedges, standardized_degree_sum]
    sorry

--traceした集合族の標準化次数和の結果の式。標準化がまちがっている。
lemma trace_normalized_degree_sum {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2) :
  normalized_degree_sum (IdealTrace.trace F x hx gcard) = Finset.sum ((all_subsets F.ground).filter (IdealTrace.trace F x hx gcard).sets) (λ s=> s.card) - (IdealTrace.trace F x hx gcard).ground.card :=
  by
    sorry

--traceでhyperedgeの数が変わらないことを言っているがこれは嘘。degreeが1の条件も使ってないし、1つ減る場合もある。
lemma trace_preserves_number_of_hyperedges {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2) :
  number_of_hyperedges (IdealTrace.trace F x hx gcard) = number_of_hyperedges F - 1 :=
 by
   sorry

--traceでtotal sizeがどうかわるか。まったく間違っている。
lemma trace_preserves_total_size_of_hyperedges {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2) :
  total_size_of_hyperedges (IdealTrace.trace F x hx gcard) = total_size_of_hyperedges F - 1 :=
 by
    sorry

--traceしたあとと、traceしたあとの標準化次数和がどのような関係にあるか。全く間違っている。
lemma normalized_degree_sum_relation {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2) :
  normalized_degree_sum (IdealTrace.trace F x hx gcard) = normalized_degree_sum F - 1 :=
  by
    sorry

--vの次数が1であれば、全体集合以外のhyperedgeは、vを通らない。
lemma hyperedges_not_through_v {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hasGround: F.sets F.ground) :
  ∀ s, F.sets s → s ≠ F.ground → v ∉ s :=
 by
  intros ss hs hneq
  by_contra h
  have h_deg1 := deg1
  unfold degree at h_deg1
  rw [Finset.card_eq_one] at h_deg1
  obtain ⟨t, ht⟩ := h_deg1
  -- Finset.filter (fun s ↦ F.sets s = (true = true) ∧ v ∈ s) (all_subsets F.ground) = {t}
  apply hneq
  have set2inc1: F.ground ∈ (Finset.filter (fun s ↦ F.sets s = true ∧ v ∈ s) (all_subsets F.ground)):= by
    simp
    rw [all_subsets]
    constructor
    simp
    exact ⟨hasGround, hv⟩
  have set2inc2: ss ∈ (Finset.filter (fun s ↦ F.sets s = true ∧ v ∈ s) (all_subsets F.ground)):= by
    simp
    constructor
    have ssground: ss ⊆ F.ground := by
      exact F.inc_ground ss hs
    --unfold SetFamily.sets at hs
    simp_all
    rw [all_subsets]
    --rw [Finset.powerset]
    exact Finset.mem_powerset.mpr ssground
    constructor
    exact hs
    exact h

  have set2card: ({F.ground, ss}:Finset (Finset α) ).card = 2 := by
    rw [Finset.card_insert_of_not_mem]
    simp [hneq]
    by_contra
    simp_all
  let degset := Finset.filter (fun s ↦ F.sets s = true ∧ v ∈ s) (all_subsets F.ground)
  have set2card2:  ({F.ground, ss}:Finset (Finset α) ) ⊆ degset := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    cases hz with
    | inl hzx => rw [hzx]; exact set2inc1
    | inr hzy => rw [hzy]; exact set2inc2

  have set2card3: 2 ≤ degset.card := by
    rw [←set2card]
    exact Finset.card_le_card set2card2

  have deg2: degree F v >= 2 := by
    -- v ∈ F.ground かつ sets F.ground で、v ∈ sかつsets s で、s ≠ F.ground なので、degreeは2以上になる。
    dsimp [degree]
    simp [set2card3]
    simpa [degset] using set2card3
  rw [deg1 ] at deg2
  contradiction

--次数が1である性質でいえること。本来は、次数が1なので、全体集合以外は、traceしてもhyperedgeの数も大きさもかわらないことを証明すればよい。
--lemma degree_one_property {α : Type} [DecidableEq α] [Fintype α]
--  (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (deg1: degree F x = 1) :
--  ∃ s, s ∈ F.sets ∧ x ∈ s ∧ ∀ t ∈ F.sets, x ∈ t → t = s :=
--def trace {α : Type} [DecidableEq α] [Fintype α] (F : SetFamily α) (x : α) (hx: x ∈ F.ground) (gcard: F.ground.card ≥ 2):

lemma trace_hyperedge_equiv {α : Type} [DecidableEq α] [Fintype α]
  (F : SetFamily α) (v : α) (hv: v ∈ F.ground) (deg1: degree F v = 1) (hnot: ¬(F.sets (F.ground.erase v))) (gcard: F.ground.card ≥ 2) :
  (IdealTrace.trace F v hv gcard).sets = (λ s=>  (F.sets s) ∨ (s = F.ground.erase v)) :=
by
  -- 証明をここに記述 degree1のときは、全体集合でなければ、vを通らないという補題を先に証明するとよさそう。
  ext s
  constructor
  --traceにほうに入っている場合に、元の集合族に入っているかを示す。
  intro h --(IdealTrace.trace F v hv gcard).sets s
  --rw [IdealTrace.trace] at h
  let IdealTrace:= IdealTrace.trace F v hv gcard
    --ここできっとlemma hyperedges_not_through_vを使うのでは。




  --unfold SetFamily.sets at h
  --cases h with --(IdealTrace.trace F v hv gcard).sets s
  --caseでどう分けられている？
  --goal F.sets s ∨ s = F.ground.erase v




  exact h.left


  exact ⟨h, hnot⟩
  right
  exact h
  intro h
  cases h
  exact or.inl h.1
  exact or.inr h


end Mathematics
