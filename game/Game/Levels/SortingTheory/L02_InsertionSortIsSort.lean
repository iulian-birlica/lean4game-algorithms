import Game.Metadata
import Game.Support.Clockwork
import Game.Support.SortBasics
import Game.Levels.InsertionSort.L17_InsertionSortCost
import Game.Levels.SortingTheory.L01_SortingContractAndAgreement

open Game.Clockwork

World "SortingTheory"
Level 2
Title "Insertion Sort Is a Sorting Function"

Introduction "Time to connect insertion sort to the final theory. Recall the shared
contract `Game.Clockwork.IsSort f`: it holds when `f s` is a permutation
of `s` and is sorted, for every `s`. We have already proved both halves for
insertion sort, so bundling them shows `IsSort insertionSort`. From here the
agreement theorem applies: insertion sort agrees with *every* correct sort."

/-- Insertion sort satisfies the shared sorting contract. -/
Statement insertionSort_isSort : IsSort insertionSort := by
  Hint "Unfold `IsSort` by introducing `s`, then pair the two facts you already
  proved: `insertionSort_perm` and `insertionSort_sorted`."
  intro s
  exact ⟨insertionSort_perm s, insertionSort_sorted s⟩

Conclusion "Insertion sort is now a first-class `IsSort` — subject to the
uniqueness theorem shared by all sorts."

NewTactic intro exact
NewTheorem insertionSort_perm insertionSort_sorted insertionSort_isSort
