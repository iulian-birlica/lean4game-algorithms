import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.InsertionSort.L08_InsertCorrect

open Game.Clockwork

World "InsertionSort"
Level 9
Title "Insertion Sort Rearranges"

Introduction "The second function recursively sorts the tail and inserts the
head. Prove that the complete sort is a permutation of its input."

/-- Insertion sort preserves all input elements and their multiplicities. -/
Statement insertionSort_perm (s : List ℕ) :
    List.Perm (insertionSort s) s := by
  Hint "Induct on `s`, then compose `insert_perm` with the induction hypothesis."
  induction' s with x xs ih
  · exact List.Perm.refl []
  · simp only [insertionSort]
    exact (insert_perm x (insertionSort xs)).trans (List.Perm.cons x ih)

Conclusion "The complete sort only rearranges its input."

NewDefinition Game.Clockwork.insertionSort
NewTactic induction' simp exact
NewTheorem insert_perm List.Perm.cons List.Perm.refl insertionSort_perm
