import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L16_InsertCostSorted

open Game.Clockwork

World "InsertionSort"
Level 17
Title "Insertion Sort Is Quadratic"

Introduction "`Game.Clockwork.insertionSortCost` totals the comparisons
performed across all insertions. Feed the per-step bound from Level 16 into the
induction to prove the classic worst-case bound: the whole sort uses at most `n²`
comparisons."

/-- Insertion sort performs at most a quadratic number of comparisons. -/
Statement insertionSortCost_le (s : List ℕ) :
    insertionSortCost s ≤ s.length * s.length := by
  Hint "Induct on `s`. In the step case, bound the new insertion's cost with
  `insertCost_insertionSort_le` and finish with `nlinarith`."
  induction' s with x xs ih
  · simp [insertionSortCost]
  · simp only [insertionSortCost, List.length_cons]
    nlinarith [ih, insertCost_insertionSort_le x xs]

Conclusion "Verified: insertion sort runs in at most a quadratic number of
comparisons — a fully analysed, correct sorting algorithm."

NewDefinition Game.Clockwork.insertionSortCost
NewTactic induction' simp nlinarith
NewTheorem insertCost_insertionSort_le insertionSortCost_le
