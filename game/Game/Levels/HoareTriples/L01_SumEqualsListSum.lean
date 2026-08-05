import Game.Metadata
import Game.Support.Contracts

World "HoareTriples"
Level 1
Title "Sum Equals List Sum"
-- source: RequestProject Lab01.sum_spec (ported from game W01-L01)

Introduction "The foundry's `sum` routine must match the standard library's
`List.sum`. Repair the seal by unfolding both sides."

Statement (values : List Int) : Game.Contracts.sum values = values.sum := by
  Hint "Unfold both the implementation `Game.Contracts.sum` and `List.sum`."
  Hint (hidden := true) "Use `rw [Game.Contracts.sum, List.sum]`."
  rw [Game.Contracts.sum, List.sum]

Conclusion "Verified. The contract holds for every list."

NewDefinition Game.Contracts.sum List.sum
