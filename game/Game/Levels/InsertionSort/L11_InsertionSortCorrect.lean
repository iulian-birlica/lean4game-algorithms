import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L10_InsertionSortSorted

open Game.Clockwork

World "InsertionSort"
Level 11
Title "Insertion Sort Correctness"

Introduction "Assemble the final correctness statement: the result is both a
permutation of the input and sorted."

/-- Full functional correctness of insertion sort. -/
Statement insertionSort_correct (s : List ℕ) :
    List.Perm (insertionSort s) s ∧ (insertionSort s).Pairwise (· ≤ ·) := by
  exact ⟨insertionSort_perm s, insertionSort_sorted s⟩

Conclusion "Verified: insertion sort returns a sorted permutation of its input."

NewTactic exact
NewTheorem insertionSort_perm insertionSort_sorted insertionSort_correct
