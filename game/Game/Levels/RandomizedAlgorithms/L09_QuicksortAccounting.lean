import Game.Metadata
import Game.Support.Randomized

open Game.Randomized

World "RandomizedAlgorithms"
Level 9
Title "Quicksort Harmonic Step"
-- source: ../game/Game/Worlds/W10Randomized/L09QuicksortAccounting.lean

Introduction "Unfold the next step of the harmonic upper bound
`2 n H_n` for randomized quicksort."

Statement (n : Nat) :
    quicksortExpectedComparisons (n + 1) =
      2 * (n + 1) * (Game.Randomized.harmonic n + (1 : ℚ) / (n + 1)) := by
  Hint "This is exactly the successor clause of `harmonic` after unfolding
  `quicksortExpectedComparisons`."
  rw [quicksortExpectedComparisons, Game.Randomized.harmonic]
  push_cast
  rfl

Conclusion "The harmonic accounting step is exposed."

NewDefinition Game.Randomized.quicksortExpectedComparisons Game.Randomized.harmonic
