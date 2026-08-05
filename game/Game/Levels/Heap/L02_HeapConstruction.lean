import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "Heap"
Level 2
Title "Heap Construction"
-- source: RequestProject Lab15.buildHeap_isHeap, Lab15.elems_buildHeap

Introduction "`buildHeap` folds `insert` over a list, right to left,
starting from the empty heap. Since `insert` maintains the heap invariant
(`insert_isHeap`, by merging in a singleton) and adds exactly one key
(`elems_insert`), building a heap this way both stays a heap and loses no
elements."

Statement (l : List ℕ) : IsHeap (buildHeap l) ∧ elems (buildHeap l) ~ l := by
  Hint "Prove each fact by induction on `l`, independently — the step case of each converts to
  the corresponding `insert` fact applied to the induction hypothesis."
  constructor
  · induction' l with x l ih
    · trivial
    · convert insert_isHeap x ih using 1
  · induction' l with x l ih
    · rfl
    · convert List.Perm.trans (elems_insert x (buildHeap l)) (List.Perm.cons x ih) using 1

Conclusion "Verified: building a heap by repeated insertion stays a heap, and loses nothing."

NewDefinition Game.Clockwork.buildHeap
NewTheorem Game.Clockwork.insert_isHeap Game.Clockwork.elems_insert
