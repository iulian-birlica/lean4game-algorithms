import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L13_InsertionSortLength

open Game.Clockwork

World "InsertionSort"
Level 14
Title "Sorting Preserves Membership"

Introduction "A permutation contains exactly the same elements, so membership
in the sorted list is the same as membership in the input. Reuse the
permutation result from Level 9 rather than re-inducting."

/-- An element belongs to the sorted list exactly when it belongs to the input. -/
Statement insertionSort_mem (a : ℕ) (s : List ℕ) :
    a ∈ insertionSort s ↔ a ∈ s := by
  Hint "`insertionSort_perm` gives the permutation; `List.Perm.mem_iff` turns it
  into a membership equivalence."
  exact (insertionSort_perm s).mem_iff

Conclusion "Sorting preserves exactly the set of elements present."

NewTactic exact
NewTheorem insertionSort_perm List.Perm.mem_iff insertionSort_mem
