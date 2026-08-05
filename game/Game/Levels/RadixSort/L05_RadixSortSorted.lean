import Game.Metadata
import Game.Support.RadixSort
import Game.Levels.RadixSort.L04_RadixSortKey

open Game.Clockwork

World "RadixSort"
Level 5
Title "Radix Sort Sorts"

Introduction "Finally, connect sorting by bits to sorting by value. If every
element is below `2 ^ n`, then `a % 2 ^ n = a`, so sorting by the low `n` bits is
the same as sorting outright. Use `radixSort_perm` to see that the output's
elements are exactly the input's, so the bound applies to them."

/-- Radix sort with `n` passes fully sorts any list whose elements are all below
`2 ^ n`. -/
Statement radixSort_sorted (n : ℕ) (s : List ℕ) (h : ∀ x ∈ s, x < 2 ^ n) :
    (binaryRadixSort n s).Pairwise (· ≤ ·) := by
  Hint "Start from `radixSort_pairwise_key` and upgrade with
  `List.Pairwise.imp_of_mem`. Transport membership back to `s` via
  `radixSort_perm`, then rewrite each key using `Nat.mod_eq_of_lt`."
  refine (radixSort_pairwise_key n s).imp_of_mem ?_
  intro a b ha hb hab
  have hamem : a ∈ s := (radixSort_perm n s).mem_iff.mp ha
  have hbmem : b ∈ s := (radixSort_perm n s).mem_iff.mp hb
  rwa [Nat.mod_eq_of_lt (h a hamem), Nat.mod_eq_of_lt (h b hbmem)] at hab

Conclusion "Radix sort — a non-comparison sort — returns a sorted list."

NewTactic refine intro rwa
NewTheorem radixSort_pairwise_key List.Pairwise.imp_of_mem radixSort_perm
  List.Perm.mem_iff Nat.mod_eq_of_lt radixSort_sorted
