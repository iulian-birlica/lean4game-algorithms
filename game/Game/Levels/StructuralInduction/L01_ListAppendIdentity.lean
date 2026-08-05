import Game.Metadata
import Game.Support.Induction

World "StructuralInduction"
Level 1
Title "List Append Identity"
-- source: RequestProject Lab02.app_nil

Introduction "
`Game.Induction.List` is our hand-rolled list type, so the base/step shape
of induction is completely explicit. Start with the simplest append fact:
putting `nil` on the right should change nothing.
"

Statement {α : Type} (xs : Game.Induction.List α) :
    Game.Induction.List.append xs Game.Induction.List.nil = xs := by
  Hint "Induct on `xs`."
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    Hint (hidden := true) "Unfold `append` and rewrite with the induction hypothesis."
    rw [Game.Induction.List.append, ih]

Conclusion "Verified: `nil` really is a right identity for append."

NewDefinition Game.Induction.List Game.Induction.List.append
  Game.Induction.List.nil Game.Induction.List.cons
NewTheorem Game.Induction.List.append_nil
