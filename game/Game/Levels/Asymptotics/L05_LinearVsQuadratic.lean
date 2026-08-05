import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L04_ConstantAndLinearGrowth

open Game.Clockwork

World "Asymptotics"
Level 5
Title "Linear vs. Quadratic"

Introduction "Among powers of `n`, the larger exponent eventually wins.
Start with the first step: linear growth is eventually bounded by
quadratic growth."

/-- Linear growth is eventually dominated by quadratic growth. -/
Statement linear_isBigO_quadratic : rpol 1 =O rpol 2 := by
  Hint "Again use `C = 1` and `N = 1`."
  use 1
  · norm_num
  use 1
  intro n hn
  Hint (hidden := true) "Rewrite the left-hand absolute value with `abs_rpol_one`, and the right-hand one with `abs_of_nonneg`."
  rw [abs_rpol_one, abs_of_nonneg]
  · Hint (hidden := true) "After unfolding `rpol`, convert `hn` to a real inequality and let `nlinarith` use `1 ≤ n`."
    norm_num [rpol]
    norm_cast at hn
    nlinarith
  · Hint (hidden := true) "Quadratic costs are nonnegative."
    norm_num [rpol]
    positivity

Conclusion "Each extra power of `n` pushes the function up the growth
hierarchy."

NewTactic positivity nlinarith
NewTheorem linear_isBigO_quadratic
