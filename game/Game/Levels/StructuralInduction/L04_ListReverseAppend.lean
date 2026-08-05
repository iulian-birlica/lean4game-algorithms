import Game.Metadata
import Game.Support.Induction

World "StructuralInduction"
Level 4
Title "List Reverse Append"
-- source: RequestProject Lab02.rev_app

Introduction "Now prove that reversing an append flips the order of the two
parts. This is the first proof that really combines earlier cards:
`append_nil` handles the base case, and `append_assoc` closes the step case."

Statement {α : Type} (xs ys : Game.Induction.List α) :
    Game.Induction.List.rev (Game.Induction.List.append xs ys)
      = Game.Induction.List.append (Game.Induction.List.rev ys) (Game.Induction.List.rev xs) := by
  Hint "Induct on `xs`."
  induction xs with
  | nil =>
    Hint (hidden := true) "Unfold `append` and `rev`, then use `append_nil`."
    rw [Game.Induction.List.append, Game.Induction.List.rev, Game.Induction.List.append_nil]
  | cons x xs ih =>
    Hint (hidden := true) "Unfold `append` and `rev`, rewrite with the induction hypothesis, then use `append_assoc`."
    rw [Game.Induction.List.append, Game.Induction.List.rev, ih, Game.Induction.List.rev,
      Game.Induction.List.append_assoc]

Conclusion "Verified: reversing an append reverses the order of its pieces."

NewDefinition Game.Induction.List.rev
NewTheorem Game.Induction.List.rev_append
