import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L08_BigOCalculus

open Game.Clockwork

World "Asymptotics"
Level 12
Title "Chaining Growth Bounds"

Introduction "Once you know a few basic comparisons, transitivity lets you
assemble stronger ones. Combine the earlier rooms to show that constants are
`O(n²)`, linear functions are `O(n³)`, and even constants are `O(e^n)`."

/-- Earlier asymptotic comparisons can be chained into stronger ones. -/
Statement growth_chain :
    (fun _ => (1 : ℝ)) =O rpol 2 ∧ rpol 1 =O rpol 3 ∧ (fun _ => (1 : ℝ)) =O rexp := by
  Hint "Use the transitivity half of `bigO_calculus`, together with the
  comparison theorems you already proved."
  constructor
  · exact
      (bigO_calculus (f := fun _ => (1 : ℝ)) (g := rpol 1) (h := rpol 2)).2
        constant_isBigO_linear linear_isBigO_quadratic
  · constructor
    · exact
        (bigO_calculus (f := rpol 1) (g := rpol 2) (h := rpol 3)).2
          linear_isBigO_quadratic quadratic_isBigO_cubic
    · exact
        (bigO_calculus (f := fun _ => (1 : ℝ)) (g := rpol 1) (h := rexp)).2
          constant_isBigO_linear linear_isBigO_exponential

Conclusion "A small library of asymptotic facts makes later reasoning much
shorter."

NewTheorem constant_isBigO_linear linear_isBigO_quadratic quadratic_isBigO_cubic
  linear_isBigO_exponential bigO_calculus growth_chain
