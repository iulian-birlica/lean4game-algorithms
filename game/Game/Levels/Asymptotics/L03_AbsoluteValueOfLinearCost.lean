import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L02_PowerOne

open Game.Clockwork

World "Asymptotics"
Level 3
Title "Absolute Value of a Cost"

Introduction "Asymptotic notation uses absolute values, so the next step is
to simplify them when the cost function is already nonnegative."

/-- The linear cost `rpol 1 n` is nonnegative, so its absolute value simplifies away. -/
Statement abs_rpol_one (n : ℕ) : |rpol 1 n| = rpol 1 n := by
  Hint "Rewrite `|x|` as `x` using `abs_of_nonneg`."
  rw [abs_of_nonneg]
  · rfl
  · Hint (hidden := true) "Unfold `rpol`, then use `norm_cast` to return from reals to naturals."
    norm_num [rpol]
    norm_cast
    exact Nat.zero_le n

Conclusion "For nonnegative cost functions, the absolute values in Big-O
statements often disappear immediately."

NewTactic norm_cast
NewTheorem abs_of_nonneg abs_rpol_one
