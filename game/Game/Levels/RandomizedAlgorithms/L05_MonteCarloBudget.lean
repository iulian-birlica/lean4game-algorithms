import Game.Metadata
import Game.Support.Randomized

open Game.Randomized

World "RandomizedAlgorithms"
Level 5
Title "Relax the Error Budget"
-- source: ../game/Game/Worlds/W10Randomized/L05MonteCarloBudget.lean

Introduction "If an algorithm already satisfies a smaller Monte Carlo error
budget, it also satisfies any larger one."

Statement (σ α : Type) (seeds : List σ) (run : σ → α) (good : α → Bool)
    (small large : ℚ) :
    MonteCarlo seeds run good small → small ≤ large →
    MonteCarlo seeds run good large := by
  Hint "This is just transitivity of `≤` after unfolding the definition."
  exact fun h_small h_le => le_trans h_small h_le

Conclusion "Increasing the allowed error preserves the guarantee."

NewDefinition Game.Randomized.MonteCarlo
