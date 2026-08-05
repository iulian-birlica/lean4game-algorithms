import Game.Metadata
import Game.Support.Design

open Game.Design

World "DynamicProgramming"
Level 6
Title "Minimum Lower Bound"
-- source: RequestProject Lab06.le_cmin

Introduction "To prove something is below a minimum, prove it is below both
choices. This level isolates that lower-bound rule for `cmin`."

Statement (a b c : ℕ∞) (ha : c ≤ a) (hb : c ≤ b) : c ≤ cmin a b := by
  Hint "Again, unfold `cmin` and case on whether `a ≤ b`; each branch is one
  of the hypotheses."
  unfold cmin
  by_cases h : a ≤ b
  · rw [if_pos h]
    exact ha
  · rw [if_neg h]
    exact hb

Conclusion "A lower bound for both branches is a lower bound for their
minimum."
