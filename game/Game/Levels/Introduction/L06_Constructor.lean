import Game.Metadata

World "Intro"
Level 6
Title "Constructor"

Introduction "When the goal has more than one field, `constructor` breaks it
into the pieces you must prove.
For a conjunction, that means one goal for the left half and one for the
right half."

Statement : ∀ p q : Prop, p → q → q ∧ p := by
  intro p q hp hq
  Hint "Split the conjunction into its two required goals."
  constructor
  · exact hq
  · exact hp

Conclusion "The conjunction closed once both constructor-generated goals were proved."

NewTactic constructor
OnlyTactic intro exact constructor
