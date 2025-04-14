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

      · --hyperedgeがxを含んでいたか、含んでなかったかで、場合分けする必要があるか？
        dsimp [setup_trace_spo2] at h
        dsimp [restrictedSetoid] at h
        --simp at h
        --spo_closuresystemは展開する必要があるのかないのか。展開しない場合は、何からの定理を利用することになる。
        --どちらにせよ、setsかどうかはidealで判断されるので、idealの議論は必要である。
        --fqの議論は必要なのかどうか。親が一つであることは今回のには関係してなさそう。xの極大性は関係している。
        --元々のidealがxを含む場合と含まない場合がある。xの同値類の大きさが2以上なので、xが極大になるということは使いそう。
        --xが極大の場合は、idealからxを含む同値類を除いても再びidealになる。ということを使うはず。
        --結局、xを含まないidealの全体と一致する。それに関する補題を作ってもいいかも。
        --補題。極大元xでtraceしたもののideal全体は、xを含まないideal全体と一致する。
        --toNewやtoOldを展開する必要はあるか。これは、trace前の同値類と後の同値類の対応の写像。
        --利用するのであれば、定理を作りたいところ。
        --setoidで同値の頂点は、入るか入らないかが同時ということも使う可能性あり。
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
