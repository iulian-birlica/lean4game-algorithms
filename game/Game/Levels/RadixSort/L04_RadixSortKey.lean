import Game.Metadata
import Game.Support.RadixSort
import Game.Levels.RadixSort.L03_BitPassStep

open Game.Clockwork

World "RadixSort"
Level 4
Title "Sorted by the Low Bits"

Introduction "Iterate the refinement step: after `n` passes, the list is sorted
by its low `n` bits. The base case is vacuous — every element has the same low
`0` bits (`a % 2 ^ 0 = a % 1 = 0`)."

/-- After `n` passes, radix sort is sorted by the low `n` bits of each element. -/
Statement radixSort_pairwise_key (n : ℕ) (s : List ℕ) :
    (binaryRadixSort n s).Pairwise (fun a b => a % 2 ^ n ≤ b % 2 ^ n) := by
  Hint "Induct on `n`. The base case follows from `List.pairwise_of_forall_sublist`
  and `Nat.mod_one`; the step case is exactly `bitPass_pairwise_step`."
  induction n with
  | zero =>
    apply List.pairwise_of_forall_sublist
    intro a b _
    simp [Nat.mod_one]
  | succ k ih => exact bitPass_pairwise_step k (binaryRadixSort k s) ih

Conclusion "Radix sort sorts by successively longer prefixes of the bits."

NewTactic induction apply intro simp exact
NewTheorem List.pairwise_of_forall_sublist Nat.mod_one bitPass_pairwise_step
  radixSort_pairwise_key
