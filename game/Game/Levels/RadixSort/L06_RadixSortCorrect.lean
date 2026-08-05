import Game.Metadata
import Game.Support.RadixSort
import Game.Levels.RadixSort.L05_RadixSortSorted

open Game.Clockwork

World "RadixSort"
Level 6
Title "Radix Sort Correctness"

Introduction "Assemble the final correctness statement: given enough bits, radix
sort returns a sorted permutation of its input — exactly the same specification
proved for the comparison sorts, even though radix sort never compares two
elements."

/-- Full functional correctness of radix sort. -/
Statement radixSort_correct (n : ℕ) (s : List ℕ) (h : ∀ x ∈ s, x < 2 ^ n) :
    List.Perm (binaryRadixSort n s) s ∧ (binaryRadixSort n s).Pairwise (· ≤ ·) := by
  exact ⟨radixSort_perm n s, radixSort_sorted n s h⟩

Conclusion "Verified: radix sort meets the same sorted-permutation specification
as insertion and selection sort — the shared contract we will unify next."

NewTactic exact
NewTheorem radixSort_perm radixSort_sorted radixSort_correct
