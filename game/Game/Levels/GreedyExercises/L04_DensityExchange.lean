import Game.Metadata
import Game.Support.Design

open Game.Design

World "GreedyExercises"
Level 4
Title "Density Exchange"

Introduction "The greedy knapsack proof uses one local exchange step over and
over: once the head material has maximum density, scaling another material by a
nonnegative amount preserves that density bound."

/-- Scaling a lower-density material by a nonnegative amount preserves the head-density bound. -/
Statement (best : Item) (rest : List Item) (other : Item) (amount : ℝ)
    (hpos : PosWeights (best :: rest))
    (hsorted : SortedByDensity (best :: rest))
    (hother : other ∈ best :: rest)
    (hamount : 0 ≤ amount) :
    amount * other.v ≤ amount * ((best.v / best.w) * other.w) := by
  Hint "Use `density_bound_of_sorted` to compare `other` with the head item,
  then multiply that inequality by the nonnegative `amount`."
  have hden : other.v ≤ (best.v / best.w) * other.w :=
    density_bound_of_sorted best rest hpos hsorted other hother
  exact mul_le_mul_of_nonneg_left hden hamount

Conclusion "The density comparison survives scaling, which is the algebraic core of the exchange argument."

NewTactic exact «have»
NewDefinition Game.Design.Item Game.Design.Item.w Game.Design.Item.v
  Game.Design.PosWeights Game.Design.SortedByDensity
NewTheorem Game.Design.density_bound_of_sorted mul_le_mul_of_nonneg_left
