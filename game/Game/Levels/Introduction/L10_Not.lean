import Game.Metadata

World "Intro"
Level 10
Title "Not"

Introduction "Negation is just implication to falsehood.
So if you know `¬ p` and later also get a proof of `p`, you can apply the
negation as a function."

Statement : ∀ p : Prop, ¬ p → p → False := by
  intro p hnp hp
  Hint "Apply the negation hypothesis to the proof of `{p}`."
  exact hnp hp

Conclusion "A negation becomes useful once you feed it the thing it rules out."

OnlyTactic intro exact
