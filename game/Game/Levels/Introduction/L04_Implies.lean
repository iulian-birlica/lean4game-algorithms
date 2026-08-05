import Game.Metadata

World "Intro"
Level 4
Title "Implies"

Introduction "
Now we get to actually use a hypothesis.
TODO: Explain the Curry-Howard correspondence and how Lean takes it to the full effect.
TODO: Explain that you can use `intro` with an implication as well.
Use `intro` to introduce hypotheses into your local context.
Use `exact` to finish your goal by using your hypothesis.
TODO: We should also explain `apply`.
"

Statement : ∀ p : Prop, p → p := by
  Hint "Introduce the proposition and the premise."
  intro p h
  Hint (hidden := true) "You now have `{h} : {p}` in context — close the goal with it."
  exact h

Conclusion "Any hypothesis is itself a proof of what it asserts."

NewTactic intro exact
OnlyTactic intro exact
