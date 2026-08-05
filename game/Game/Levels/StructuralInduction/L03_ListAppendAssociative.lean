import Game.Metadata
import Game.Support.Induction

World "StructuralInduction"
Level 3
Title "List Append Associative"
-- source: RequestProject Lab02.app_assoc

Introduction "Now there are three lists at once. Show that re-parenthesizing
append does not change the result."

Statement {α : Type} (xs ys zs : Game.Induction.List α) :
    Game.Induction.List.append (Game.Induction.List.append xs ys) zs
        = Game.Induction.List.append xs (Game.Induction.List.append ys zs) := by
  Hint "Induct on `xs`."
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    Hint (hidden := true) "Unfold `append` on both sides and rewrite with the induction hypothesis."
    rw [Game.Induction.List.append, Game.Induction.List.append, Game.Induction.List.append, ih]

Conclusion "Verified: append is associative."

NewTheorem Game.Induction.List.append_assoc
