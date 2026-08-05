import Game.Metadata

World "Intro"
Level 1
Title "Read the Goal"

Introduction "
TODO: These levels should work towards creating the original lean4 cheatsheet, that you can give afterwards.
TODO: Lean description
TODO: Remember the reflexivity property of '='.
TODO: Explain the goal and hypotheses distinction.
Every proof starts with reading the goal.
Here Lean can compute both sides of the equation directly — no cleverness required.
"

Statement : (4 : ℕ)  = 4 := by
  Hint "TODO: Modify this goal. Let Lean compute both sides."
  Hint (hidden := true) "Use `rfl`."
  rfl

Conclusion "The goal was true by computation alone."

NewTactic rfl
OnlyTactic rfl
