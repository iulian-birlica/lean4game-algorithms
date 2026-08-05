import Game.Metadata
import Game.Support.SelectionSort
import Game.Levels.SelectionSort.L05_SelectionSortSorted

open Game.Clockwork

World "SelectionSort"
Level 6
Title "Selection Sort Correctness"

Introduction "Assemble the final correctness statement: the result of selection
sort is both a permutation of the input and sorted."

/-- Full functional correctness of selection sort. -/
Statement selectionSort_correct (s : List ℕ) :
    List.Perm (selectionSort s) s ∧ (selectionSort s).Pairwise (· ≤ ·) := by
  exact ⟨selectionSort_perm s, selectionSort_sorted s⟩

Conclusion "Verified: selection sort returns a sorted permutation of its input."

NewTactic exact
NewTheorem selectionSort_perm selectionSort_sorted selectionSort_correct
