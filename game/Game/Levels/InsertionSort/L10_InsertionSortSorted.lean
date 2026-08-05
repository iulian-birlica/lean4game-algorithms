import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L09_InsertionSortPerm

open Game.Clockwork

World "InsertionSort"
Level 10
Title "Insertion Sort Sorts"

Introduction "Finally prove that the complete output is sorted. The induction
hypothesis sorts the tail, and `insert_sorted` preserves that invariant when
the head is inserted."

/-- The output of insertion sort is sorted. -/
Statement insertionSort_sorted (s : List ℕ) :
    (insertionSort s).Pairwise (· ≤ ·) := by
  Hint "Induct on `s` and apply `insert_sorted` in the step case."
  induction' s with x xs ih
  · exact List.Pairwise.nil
  · simp only [insertionSort]
    exact insert_sorted x (insertionSort xs) ih

Conclusion "Insertion sort always returns a sorted list."

NewTactic induction' simp exact
NewTheorem List.Pairwise.nil insert_sorted insertionSort_sorted
