import Game.Metadata
import Game.Support.SelectionSort
import Game.Levels.SelectionSort.L04_SelectionSortPerm

open Game.Clockwork

World "SelectionSort"
Level 5
Title "Selection Sort Sorts"

Introduction "Prove that the output is sorted. The head of each step is the
minimum of the remaining elements (`select_min`), and those remaining elements
end up — after sorting — as a permutation of `select`'s leftovers, so the head
bounds them all."

/-- The output of selection sort is sorted. -/
Statement selectionSort_sorted (s : List ℕ) :
    (selectionSort s).Pairwise (· ≤ ·) := by
  Hint "Induct with `selectionSort.induct`. After `rw [selectionSort,
  List.pairwise_cons]`, bound the head using `select_min`, transporting
  membership back through `selectionSort_perm`."
  induction s using selectionSort.induct with
  | case1 => simp [selectionSort]
  | case2 x xs p ih =>
    rw [selectionSort, List.pairwise_cons]
    refine ⟨?_, ih⟩
    intro a ha
    exact select_min x xs a ((selectionSort_perm _).mem_iff.mp ha)

Conclusion "Selection sort always returns a sorted list."

NewTactic induction simp rw refine intro exact
NewTheorem List.pairwise_cons select_min selectionSort_perm List.Perm.mem_iff selectionSort_sorted
