import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "Heap"
Level 3
Title "Heap Sort Correctness"
-- source: RequestProject Lab15.heapSort_sorted, Lab15.heapSort_agrees_with_mergeSort

Introduction "**Heapsort**: build a heap, then repeatedly pop the maximum
(giving a decreasing list, `popAll_sorted`), and reverse to ascending.
Prove it sorts, then — via uniqueness of the sorted permutation — that it
agrees with merge sort."

Statement (l : List ℕ) :
    (heapSort l).Pairwise (· ≤ ·) ∧ heapSort l = (mergeSortT l).ret := by
  Hint "Prove sortedness first, from `popAll_sorted`/`buildHeap_isHeap` reversed via
  `List.pairwise_reverse`; the equality then follows from `sorted_perm_unique` fed heapsort's own
  permutation fact `heapSort_perm`."
  have hsorted : (heapSort l).Pairwise (· ≤ ·) :=
    List.pairwise_reverse.mpr (popAll_sorted _ (buildHeap_isHeap _))
  refine ⟨hsorted, ?_⟩
  refine sorted_perm_unique hsorted (mergeSortT_sorted l) ?_
  exact (heapSort_perm l).trans (mergeSortT_perm l).symm

Conclusion "Verified: heapsort is provably correct, and agrees with merge sort."

NewDefinition Game.Clockwork.heapSort
NewTheorem Game.Clockwork.popAll_sorted Game.Clockwork.buildHeap_isHeap
  Game.Clockwork.heapSort_perm List.pairwise_reverse
