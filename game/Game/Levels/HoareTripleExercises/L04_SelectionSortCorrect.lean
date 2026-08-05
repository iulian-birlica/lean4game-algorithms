import Game.Metadata
import Game.Support.Contracts

World "HoareTripleExercises"
Level 4
Title "Selection Sort Correctness"
-- source: RequestProject Lab04.selectionSort_spec

Introduction "`selectionSort` repeatedly pulls out the minimum of the
unsorted suffix. Its sortedness and permutation proofs are supplied —
assemble the full contract from them."

Statement (l : List Int) :
    Game.Contracts.IsSorted (Game.Contracts.selectionSort l)
      ∧ (Game.Contracts.selectionSort l).Perm l := by
  Hint "Pair the two supplied cards."
  Hint (hidden := true) "Use `selectionSort_sorted` and `selectionSort_perm`."
  exact ⟨Game.Contracts.selectionSort_sorted l, Game.Contracts.selectionSort_perm l⟩

Conclusion "Verified: `selectionSort` produces a sorted permutation, always."

NewDefinition Game.Contracts.selectionSort
NewTheorem Game.Contracts.selectionSort_sorted Game.Contracts.selectionSort_perm
