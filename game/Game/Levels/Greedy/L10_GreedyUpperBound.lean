import Game.Metadata
import Game.Support.Design
import Game.Levels.Greedy.L09_GreedyValueWitness

open Game.Design

World "Greedy"
Level 10
Title "Greedy Upper Bound"
-- source: RequestProject Lab05.greedy_upper_bound

Introduction "The converse direction is the hard upper-bound fact: under
sorted density and non-negative values, no feasible choice can beat the greedy
value."

Statement greedy_choice_upper_bound (items : List Item) (c : ℝ)
    (hpos : PosWeights items) (hval : NonnegValues items)
    (hsorted : SortedByDensity items) :
    ∀ x, Feasible items c x → totalValue items x ≤ greedy items c := by
  Hint "This whole upper-bound card is supplied; introduce `x` and feed the
  feasibility proof into it."
  intro x hx
  exact greedy_upper_bound items c x hpos hval hsorted hx

Conclusion "Every feasible solution is bounded above by the greedy value."

NewDefinition Game.Design.NonnegValues
NewTheorem Game.Design.greedy_upper_bound
