import Game.Metadata
import Game.Support.PrefixStrings

open Game.String

World "PrefixStrings"
Level 9
Title "KMP Linear Budget"

Introduction "A linear KMP scan spends at most two units of work per consumed
symbol: one successful comparison advances both the consumed count and the
matched count, and the budget invariant tracks that this never runs the
comparison count ahead."

Statement (consumed matched comparisons : Nat)
    (h : WithinKMPBudget consumed matched comparisons) :
    WithinKMPBudget (consumed + 1) (matched + 1) (comparisons + 1) := by
  Hint "Unfold the budget invariant on both sides; the rest is linear
  arithmetic."
  unfold WithinKMPBudget at *
  Hint (hidden := true) "`omega`."
  omega

Conclusion "One more successful comparison stays within budget."

NewDefinition Game.String.WithinKMPBudget
