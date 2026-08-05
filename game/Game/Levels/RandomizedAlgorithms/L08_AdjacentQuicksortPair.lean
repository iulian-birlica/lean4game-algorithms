import Game.Metadata
import Game.Support.Randomized

open Game.Randomized

World "RandomizedAlgorithms"
Level 8
Title "Adjacent Quicksort Keys"
-- source: ../game/Game/Worlds/W10Randomized/L08QuicksortPair.lean

Introduction "Adjacent positions in randomized quicksort are compared with
probability one, because their interval contains only the two endpoints."

Statement (i j : Nat) :
    j = i + 1 → quicksortPairProbability i j = 1 := by
  Hint "Substitute `j = i + 1` and simplify the interval length."
  intro hj
  norm_num [quicksortPairProbability, hj]

Conclusion "Adjacent keys are compared with certainty."

NewDefinition Game.Randomized.quicksortPairProbability
