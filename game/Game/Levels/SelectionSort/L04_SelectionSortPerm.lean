import Game.Metadata
import Game.Support.SelectionSort
import Game.Levels.SelectionSort.L03_SelectMin

open Game.Clockwork

World "SelectionSort"
Level 4
Title "Selection Sort Rearranges"

Introduction "The second function, `Game.Clockwork.selectionSort`,
repeatedly pulls out the minimum with `select` and recurses on the rest. Prove
that the whole sort is a permutation of its input. Because the recursion is on
the leftover list rather than the tail, induct with the tailored principle
`selectionSort.induct`."

/-- Selection sort preserves all input elements and their multiplicities. -/
Statement selectionSort_perm (s : List ℕ) :
    List.Perm (selectionSort s) s := by
  Hint "Use `induction s using selectionSort.induct`. In the step case, unfold
  with `rw [selectionSort]` and compose `List.Perm.cons` (with the induction
  hypothesis) with `select_perm`."
  induction s using selectionSort.induct with
  | case1 => simp [selectionSort]
  | case2 x xs p ih =>
    rw [selectionSort]
    exact (List.Perm.cons _ ih).trans (select_perm x xs)

Conclusion "The complete sort only rearranges its input."

NewDefinition Game.Clockwork.selectionSort
NewTactic induction simp rw exact
NewTheorem select_perm List.Perm.cons selectionSort_perm
