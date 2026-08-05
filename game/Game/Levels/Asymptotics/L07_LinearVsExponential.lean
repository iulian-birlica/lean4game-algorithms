import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L06_QuadraticVsCubic

open Game.Clockwork

World "Asymptotics"
Level 7
Title "Linear vs. Exponential"

Introduction "Exponential growth eventually outpaces even the familiar
polynomial costs. Start with the easiest comparison: linear growth is
bounded by `e^n`."

/-- Linear growth is eventually dominated by exponential growth. -/
Statement linear_isBigO_exponential : rpol 1 =O rexp := by
  Hint "Witness `C = 1` and `N = 0`."
  use 1
  · norm_num
  use 0
  intro n hn
  Hint (hidden := true) "Rewrite the absolute values first: use `abs_rpol_one` on the left and `abs_of_nonneg` on the right."
  rw [abs_rpol_one, abs_of_nonneg]
  · Hint (hidden := true) "After unfolding `rpol` and `rexp`, use `Real.add_one_le_exp (n : ℝ)`, which says `n + 1 ≤ e^n`."
    norm_num [rpol, rexp]
    linarith [Real.add_one_le_exp (n : ℝ)]
  · norm_num [rexp]
    positivity

Conclusion "Exponential growth eventually beats linear growth."

NewDefinition Game.Clockwork.rexp
NewTheorem Real.add_one_le_exp linear_isBigO_exponential
