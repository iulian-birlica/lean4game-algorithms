import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L02_InsertLowerBound

open Game.Clockwork

World "InsertionSort"
Level 3
Title "Sortedness: Base Case"

Introduction "We are about to prove that inserting into a sorted list stays
sorted. That proof is an induction on the list, so we first isolate its pieces
as their own results. This is the base case: inserting into the empty list
produces the singleton `[x]`, which is trivially sorted."

/-- Base case of the sortedness invariant: `insert x []` is sorted. -/
Statement insert_sorted_nil (x : ℕ) :
    (Game.Clockwork.insert x ([] : List ℕ)).Pairwise (· ≤ ·) := by
  Hint "`insert x []` reduces to `[x]`; a singleton list is sorted by
  `List.pairwise_singleton`."
  exact List.pairwise_singleton _ _

Conclusion "The base case is ready to be dropped into the main induction."

NewTactic exact
NewTheorem List.pairwise_singleton insert_sorted_nil
