import Game.Metadata
import Game.Support.Design
import Game.Levels.Greedy.L10_GreedyUpperBound

open Game.Design

World "Greedy"
Level 11
Title "Greedy Optimality"
-- source: RequestProject Lab05.greedy_is_optimal

Introduction "Now the full theorem is short: one earlier result gives a
feasible assignment that attains the greedy value, and the next one says no
feasible assignment can do better."

Statement greedy_is_optimal (items : List Item) (c : ℝ)
    (hpos : PosWeights items) (hval : NonnegValues items)
    (hsorted : SortedByDensity items) (hc : 0 ≤ c) :
    (∃ x, Feasible items c x ∧ totalValue items x = greedy items c) ∧
    (∀ x, Feasible items c x → totalValue items x ≤ greedy items c) := by
  Hint "Pair the witness level with the upper-bound level."
  exact ⟨greedy_value_witness items c hpos hc,
    greedy_choice_upper_bound items c hpos hval hsorted⟩

Conclusion "Greedy is both achievable and unbeatable, so it is optimal."
