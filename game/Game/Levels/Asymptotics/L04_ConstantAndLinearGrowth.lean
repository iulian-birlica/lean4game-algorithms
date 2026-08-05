import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L03_AbsoluteValueOfLinearCost

open Game.Clockwork

World "Asymptotics"
Level 4
Title "Constants vs. Linear"
-- source: RequestProject Lab11.one_isBigO_rpol

Introduction "A constant cost eventually loses to a linear one. Prove
`1 = O(n)` by showing that once `n ≥ 1`, the constant `1` is bounded by `n`."

/-- Constant growth is asymptotically bounded by linear growth. -/
Statement constant_isBigO_linear : (fun _ => (1 : ℝ)) =O rpol 1 := by
  Hint "Witness `C = 1` and `N = 1`."
  use 1
  · norm_num
  use 1
  intro n hn
  Hint (hidden := true) "Rewrite `|1|` with `abs_of_nonneg`, and rewrite `|rpol 1 n|` with the previous level's theorem."
  rw [abs_of_nonneg, abs_rpol_one]
  · Hint (hidden := true) "After `norm_num [rpol]`, use `norm_cast` to reduce the real inequality back to `hn : 1 ≤ n`."
    norm_num [rpol]
    norm_cast
    exact hn
  · norm_num

Conclusion "Constants are asymptotically smaller than linear growth."

NewTheorem constant_isBigO_linear
