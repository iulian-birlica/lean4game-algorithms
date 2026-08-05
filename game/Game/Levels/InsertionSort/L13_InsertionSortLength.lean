import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L12_InsertLength

open Game.Clockwork

World "InsertionSort"
Level 13
Title "Sorting Preserves Length"

Introduction "Since each insertion adds one element and there is one insertion
per element of the input, the sorted list has the same length as the input."

/-- Insertion sort preserves the length of its input. -/
Statement insertionSort_length (s : List ℕ) :
    (insertionSort s).length = s.length := by
  Hint "Induct on `s` and rewrite with `insert_length` in the step case."
  induction' s with x xs ih
  · rfl
  · simp only [insertionSort]
    simp [insert_length, ih]

Conclusion "Sorting never loses or gains elements."

NewTactic induction' simp
NewTheorem insert_length insertionSort_length
