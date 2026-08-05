import Game.Metadata
import Game.Support.SelectionSort
import Game.Support.SortBasics
import Game.Levels.SelectionSort.L06_SelectionSortCorrect
import Game.Levels.SortingTheory.L01_SortingContractAndAgreement

open Game.Clockwork

World "SortingTheory"
Level 3
Title "Selection Sort Is a Sorting Function"

Introduction "As with insertion sort, we now record that selection sort meets the
shared contract `Game.Clockwork.IsSort`. Both halves are already proved, so
this is just a matter of bundling them. Once done, the agreement theorem tells
us selection sort computes exactly the same output as insertion sort — and as any
other correct sort."

/-- Selection sort satisfies the shared sorting contract. -/
Statement selectionSort_isSort : IsSort selectionSort := by
  Hint "Introduce `s`, then pair `selectionSort_perm` with `selectionSort_sorted`."
  intro s
  exact ⟨selectionSort_perm s, selectionSort_sorted s⟩

Conclusion "Selection sort is now a first-class `IsSort`, so it is
extensionally equal to insertion sort even though the two algorithms proceed
entirely differently."

NewTactic intro exact
NewTheorem selectionSort_perm selectionSort_sorted selectionSort_isSort
