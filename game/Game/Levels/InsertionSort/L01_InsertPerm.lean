import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "InsertionSort"
Level 1
Title "Insertion Rearranges"

Introduction "The helper `Game.Clockwork.insert x s` puts `x` into its ordered position.
First prove that it neither loses nor duplicates elements."

/-- Inserting one element only rearranges the resulting list. -/
Statement insert_perm (x : ℕ) (s : List ℕ) :
    List.Perm (Game.Clockwork.insert x s) (x :: s) := by
  Hint "Induct on `s`, unfold `Game.Clockwork.insert`, and split on its comparison."
  induction' s with y ys ih
  · rfl
  · simp only [Game.Clockwork.insert]
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

Conclusion "Insertion preserves every element and its multiplicity."

NewDefinition Game.Clockwork.insert List
NewTactic induction' simp split exact rfl
NewTheorem List.Perm.cons List.Perm.swap List.Perm.refl insert_perm
