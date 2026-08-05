import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.SortingTheory.L04_DecisionTreeLeaves

open Game.Clockwork

World "SortingTheory"
Level 5
Title "Comparison Sort Lower Bound"
-- source: RequestProject Lab13.comparison_sort_lower_bound

Introduction "**The comparison-sort lower bound.** Putting the shape and
information bounds together: `n! ≤ 2^height`, so `height ≥ log₂(n!)`, and
since `(n!)² ≥ nⁿ`, the height — the worst-case comparison count — is
`Ω(n log n)`. No comparison-based sort can beat merge sort
asymptotically. The factorial/logarithm estimates are supplied."

Statement (t : (n : ℕ) → DTree n) (ht : ∀ n, Sorts (t n)) :
    (fun n => (height (t n) : ℝ)) =Ω (fun n => (n : ℝ) * Real.log n) := by
  Hint "Witness `C = 2 log 2`, `N = 1`; combine the two supplied estimates
  with `nlinarith`."
  use 2 * Real.log 2, by positivity, 1
  Hint (hidden := true) "`mul_log_le_two_mul_log_factorial` and
  `log_factorial_le_height_mul_log_two` together give the bound directly."
  intro n hn
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have := mul_log_le_two_mul_log_factorial n
  have := log_factorial_le_height_mul_log_two (t n) (ht n)
  norm_num at *
  nlinarith [Real.log_pos one_lt_two]

Conclusion "Verified: comparison sorting cannot beat `Θ(n log n)`."

NewTheorem Game.Clockwork.mul_log_le_two_mul_log_factorial
  Game.Clockwork.log_factorial_le_height_mul_log_two
