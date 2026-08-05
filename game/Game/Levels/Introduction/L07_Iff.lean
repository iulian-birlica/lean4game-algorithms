import Game.Metadata

World "Intro"
Level 7
Title "Iff"

Introduction "A proof of `p ↔ q` is two implications: one from `p` to `q`,
and one from `q` to `p`.
Use `constructor` to split the equivalence into those two directions."

Statement : ∀ p q : Prop, (p → q) → (q → p) → (p ↔ q) := by
  intro p q hpq hqp
  Hint "Split the equivalence into its two implications."
  constructor
  · exact hpq
  · exact hqp

Conclusion "An `Iff` is complete once both directions have been proved."

OnlyTactic intro exact constructor
