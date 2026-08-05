import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "MergeSort"
Level 1
Title "Merge Correctness"
-- source: RequestProject Lab11.mergeSortT_sorted, Lab11.mergeSortT_perm

Introduction "**Merge sort is correct.** Before counting comparisons, prove
the semantic contract: the timed merge-sort implementation returns a
sorted permutation of its input."

Statement (l : List ℕ) : (mergeSortT l).ret.Pairwise (· ≤ ·) ∧ (mergeSortT l).ret ~ l := by
  Hint "The recursive correctness facts are supplied here as cards; combine
  sortedness and permutation into the contract students will reuse later."
  exact ⟨mergeSortT_sorted l, mergeSortT_perm l⟩

Conclusion "Verified: merge sort returns exactly the sorted version of its input."

NewDefinition Game.Clockwork.mergeSortT
NewTheorem Game.Clockwork.mergeSortT_sorted Game.Clockwork.mergeSortT_perm
  Game.Clockwork.sorted_perm_unique
