import Game.Metadata
import Game.Support.Design

open Game.Design

World "DynamicProgramming"
Level 5
Title "Minimum Chooses No More Than Left"
-- source: RequestProject Lab06.cmin_le_left

Introduction "Coin change uses `ℕ∞ = WithTop ℕ`, where `⊤` means
'impossible'. The helper `cmin a b` chooses the smaller of two such values.

Start with one fact: the chosen minimum is no larger than its left input."

Statement (a b : ℕ∞) : cmin a b ≤ a := by
  Hint "Unfold `cmin`, then case on whether `a ≤ b`."
  unfold cmin
  by_cases h : a ≤ b
  · Hint "In the `if_pos` branch, the goal becomes `a ≤ a`."
    rw [if_pos h]
  · Hint (hidden := true) "In the `if_neg` branch, `not_le.mp h` turns
    `¬ a ≤ b` into `b < a`; then `le_of_lt` weakens it to `b ≤ a`."
    rw [if_neg h]
    exact le_of_lt (not_le.mp h)

Conclusion "The minimum returned by `cmin` is always bounded by the left
candidate."

NewDefinition Game.Design.cmin
NewTheorem le_of_lt not_le
