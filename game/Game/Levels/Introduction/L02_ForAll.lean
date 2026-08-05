import Game.Metadata

World "Intro"
Level 2
Title "For all"

Introduction "
Whenever you have a property of the form '∀ h, p', you can assume h to be true,
add it to your hypotheses, and then prove the remaining goal 'p'.
Use `intro` to introduce hypotheses into your local context.
Note: In this case, we don't need to do anything with the introduced hypothesis"

Statement : ∀ h : Prop, (4 : ℕ) = 4 := by
  Hint "Let Lean compute both sides."
  Hint (hidden := true) "Use `rfl`."
  intro h
  rfl

Conclusion "The goal was true by computation alone."

NewTactic intro
OnlyTactic rfl intro
