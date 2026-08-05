import Game.Metadata

World "Intro"
Level 9
Title "Rewrite an Equality"

Introduction "When you have an equation `a = b`, you can replace `a` by `b`
anywhere in the goal using `rw`."

Statement : ∀ a b : ℕ, a = b → a + 1 = b + 1 := by
  intro a b h
  Hint "Replace `{a}` by `{b}` using `{h}`."
  rw [h]

Conclusion "Equals replaced by equals — the goal closed itself."

NewTactic rw
OnlyTactic intro rw
