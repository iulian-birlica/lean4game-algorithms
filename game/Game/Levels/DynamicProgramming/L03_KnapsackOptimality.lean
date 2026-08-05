import Game.Metadata
import Game.Support.Design

open Game.Design

World "DynamicProgramming"
Level 3
Title "Knapsack Optimality"
-- source: RequestProject Lab06.knap_is_optimal

Introduction "**The DP recurrence solves the 0/1 knapsack.** `knap items c`
is precisely the maximum total value over feasible selections: it is
attained (achievability), and it is an upper bound (optimality). Both halves
are supplied — assemble them."

Statement (items : List KItem) (c : ℕ) :
    (∃ s, KFeasible items c s ∧ selValue items s = knap items c) ∧
    (∀ s, KFeasible items c s → selValue items s ≤ knap items c) := by
  Hint "Pair the achievability card with the upper-bound card."
  Hint (hidden := true) "`⟨knap_achievable items c, fun s hs => knap_upper_bound items c s hs⟩`."
  exact ⟨knap_achievable items c, fun s hs => knap_upper_bound items c s hs⟩

Conclusion "Verified: the knapsack recurrence is provably optimal."

NewDefinition Game.Design.KFeasible
NewTheorem Game.Design.knap_achievable Game.Design.knap_upper_bound
