import Game.Metadata
import Game.Support.Contracts

World "HoareTripleExercises"
Level 3
Title "Bubble Sort Correctness"
-- source: RequestProject Lab04.bubbleSort_spec

Introduction "`bubbleSort` bubbles one pass to the end, fixes the maximum
in place, and recurses on the rest. Its sortedness and permutation proofs
are supplied — assemble the full contract from them."

Statement (l : List Int) :
    Game.Contracts.IsSorted (Game.Contracts.bubbleSort l) ∧ (Game.Contracts.bubbleSort l).Perm l := by
  Hint "Pair the two supplied cards."
  Hint (hidden := true) "Use `bubbleSort_sorted` and `bubbleSort_perm`."
  exact ⟨Game.Contracts.bubbleSort_sorted l, Game.Contracts.bubbleSort_perm l⟩

Conclusion "Verified: `bubbleSort` produces a sorted permutation, always."

NewDefinition Game.Contracts.bubbleSort
NewTheorem Game.Contracts.bubbleSort_sorted Game.Contracts.bubbleSort_perm
