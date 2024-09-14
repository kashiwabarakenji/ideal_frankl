import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
--import Mathlib.Init.Function
import Mathlib.Init.Logic
import Ideal.BasicDefinitions
import Ideal.BasicLemmas
import Ideal.IdealDeletion
import Mathlib.Data.Multiset.Basic
import LeanCopilot
--set_option maxHeartbeats 500000 -- Increase the heartbeat limit

namespace Ideal
variable {α : Type} [DecidableEq α] [Fintype α] [Nonempty α]

--証明はしたもののイマイチ何に使っていいかわからない。現状はどこにも使っていない。
theorem Finset.mem_of_mem_map {α β : Type} [DecidableEq β] (f : α → β) (s : Finset α) (b : β) (hf : Function.Injective f):
  b ∈ s.map ⟨f, hf⟩ ↔ ∃ a ∈ s, f a = b :=
by
  constructor
  -- Forward direction: If b ∈ s.map f, then there exists a ∈ s such that f a = b.
  · intro h
    -- Unfolding the definition of map and using the mem_map tactic
    rw [Finset.mem_map] at h
    -- h is an existential statement, so we use match to obtain the witness and the proof
    match h with
    | ⟨a, ha, ha_eq⟩ =>
      exact ⟨a, ha, ha_eq⟩
  -- Reverse direction: If there exists a ∈ s such that f a = b, then b ∈ s.map f.
  · intro h
    -- h is an existential statement, so we use match to obtain the witness and the proof
    match h with
    | ⟨a, ha, ha_eq⟩ =>
      -- Applying mem_map to show that b ∈ s.map f
      rw [Finset.mem_map]
      -- Provide the witness and the proof

      exact ⟨a, ha, ha_eq⟩

end Ideal
