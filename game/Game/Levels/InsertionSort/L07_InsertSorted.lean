import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L06_InsertSortedStep

open Game.Clockwork

World "InsertionSort"
Level 7
Title "Insertion Preserves Sortedness"

Introduction "Now assemble the central invariant: inserting one element into a
sorted list returns a sorted list. Because the base case (Level 3) and the
inductive step built from its two branches (Levels 4–6) are already proved, the
induction here is just a one-line call to each of those earlier results."

/-- Insertion into a sorted list remains sorted. -/
Statement insert_sorted (x : ℕ) (s : List ℕ) (hs : s.Pairwise (· ≤ ·)) :
    (Game.Clockwork.insert x s).Pairwise (· ≤ ·) := by
  Hint "Induct on `s`; hand the base case to `insert_sorted_nil` and the step
  case to `insert_sorted_cons`."
  induction' s with y ys ih
  · exact insert_sorted_nil x
  · exact insert_sorted_cons x y ys hs ih

Conclusion "Insertion preserves the sortedness invariant."

NewTactic induction' exact
NewTheorem insert_sorted_nil insert_sorted_cons insert_sorted
