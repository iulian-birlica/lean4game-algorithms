import Game.Metadata
import Game.Support.Induction

World "StructuralInduction"
Level 5
Title "Reverse Is Involutive"
-- source: RequestProject Lab02.rev_rev

Introduction "The flagship list-induction exercise: reversing twice gives
back the original list. The step case now has exactly one key card:
`rev_append` from the previous room."

Statement {α : Type} (xs : Game.Induction.List α) :
    Game.Induction.List.rev (Game.Induction.List.rev xs) = xs := by
  Hint "Induct on `xs`; the step case unfolds `rev` twice around `rev_append`."
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    Hint (hidden := true) "`rw [rev, rev_append, ih, rev, rev, append, append, append]`."
    rw [Game.Induction.List.rev, Game.Induction.List.rev_append, ih, Game.Induction.List.rev,
      Game.Induction.List.rev, Game.Induction.List.append, Game.Induction.List.append,
      Game.Induction.List.append]

Conclusion "Mirrored twice, unchanged: reversal is an involution."
