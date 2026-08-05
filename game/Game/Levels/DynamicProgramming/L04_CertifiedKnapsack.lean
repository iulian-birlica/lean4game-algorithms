import Game.Metadata
import Game.Support.Design

open Game.Design

World "DynamicProgramming"
Level 4
Title "Certified Knapsack"
-- source: RequestProject Lab06.knapImpl_correct, Lab06.knapImpl_is_optimal

Introduction "You already used `knapCarry` to prove the implementation's value
matches the recurrence. Now use that carried proof again: once `knapImpl` is
rewritten to `knap`, everything already proved about `knap` transfers for free
to the proof-carrying implementation."

Statement (items : List KItem) (c : ℕ) :
    knapImpl items c = knap items c ∧
      ((∃ s, KFeasible items c s ∧ selValue items s = knapImpl items c) ∧
        (∀ s, KFeasible items c s → selValue items s ≤ knapImpl items c)) := by
  Hint "Read off the bundled proof first, then rewrite the optimality theorem
  through it."
  have h : knapImpl items c = knap items c := (knapCarry items c).2.symm
  refine ⟨h, ?_⟩
  Hint (hidden := true) "`rw [h]; exact knap_is_optimal items c`."
  rw [h]
  exact knap_is_optimal items c

Conclusion "Certified: the proof-carrying knapsack is optimal, for free."

NewTheorem Game.Design.knap_is_optimal
