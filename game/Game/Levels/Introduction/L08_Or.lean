import Game.Metadata

World "Intro"
Level 8
Title "Or"

Introduction "A proof of `p ∨ q` means one side is enough.
Use `left` if you can prove the left disjunct, or `right` if you can prove
the right one."

Statement : ∀ p q : Prop, p → p ∨ q := by
  intro p q hp
  Hint "Choose the left side of the disjunction."
  left
  exact hp

Conclusion "To prove an `Or`, it is enough to commit to one side and prove it."

NewTactic left right
OnlyTactic intro exact left right
