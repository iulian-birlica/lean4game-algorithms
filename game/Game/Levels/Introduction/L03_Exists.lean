import Game.Metadata

World "Intro"
Level 3
Title "Exists"

Introduction "
TODO: Better text.

We can treat exists with `use`.
"
Statement : ∃ (x : ℕ), (2 : ℕ) + x = 4 := by
  Hint "What natural number satisfies the sum?"
  Hint (hidden := true) "Use `use 2`."
  use 2

Conclusion "We now know how to treat '∃'."

NewTactic use
OnlyTactic rfl use intro
