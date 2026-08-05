import Game.Metadata
import Game.Support.RadixSort
import Game.Levels.RadixSort.L01_BitPassPerm

open Game.Clockwork

World "RadixSort"
Level 2
Title "Radix Sort Rearranges"

Introduction "`Game.Clockwork.binaryRadixSort n s` applies `bitPass` for bits
`0` through `n - 1`. Since it is just a composition of passes, it too only
rearranges the input."

/-- Radix sort is a permutation of its input. -/
Statement radixSort_perm (n : ℕ) (s : List ℕ) : List.Perm (binaryRadixSort n s) s := by
  Hint "Induct on `n`. The step case composes `bitPass_perm` with the induction
  hypothesis."
  induction n with
  | zero => exact List.Perm.refl s
  | succ k ih => exact (bitPass_perm k (binaryRadixSort k s)).trans ih

Conclusion "The complete radix sort only rearranges its input."

NewDefinition Game.Clockwork.binaryRadixSort
NewTactic induction exact
NewTheorem bitPass_perm List.Perm.refl List.Perm.trans radixSort_perm
