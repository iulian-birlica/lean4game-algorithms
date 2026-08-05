import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L05_LinearVsQuadratic

open Game.Clockwork

World "Asymptotics"
Level 6
Title "Quadratic vs. Cubic"

Introduction "The next rung of the hierarchy is similar: a quadratic cost is
eventually bounded by a cubic one."

/-- Quadratic growth is eventually dominated by cubic growth. -/
Statement quadratic_isBigO_cubic : rpol 2 =O rpol 3 := by
  Hint "Use the same witnesses as before: `C = 1` and `N = 1`."
  use 1
  · norm_num
  use 1
  intro n hn
  Hint (hidden := true) "Rewrite both absolute values using `abs_of_nonneg`."
  rw [abs_of_nonneg, abs_of_nonneg]
  · Hint (hidden := true) "After unfolding `rpol`, convert `hn` with `norm_cast`, then use `nlinarith` on `n^2 ≤ n^3`."
    norm_num [rpol]
    norm_cast at hn
    nlinarith
  · norm_num [rpol]
    positivity
  · norm_num [rpol]
    positivity

Conclusion "Higher-degree polynomials eventually dominate lower-degree ones."

NewTheorem quadratic_isBigO_cubic
