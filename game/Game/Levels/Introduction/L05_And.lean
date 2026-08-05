import Game.Metadata

World "Intro"
Level 5
Title "And"

Introduction "A proof of `p ∧ q` is a pair: a proof of `p` and a proof of `q`.
Use `constructor` to split the goal into its two components."

Statement : ∀ p q : Prop, p → q → p ∧ q := by
  intro p q hp hq
  Hint "Split the conjunction into two goals."
  constructor
  · exact hp
  · exact hq

Conclusion "Evidence assembled: both halves proved."

NewTactic constructor
OnlyTactic intro exact constructor
