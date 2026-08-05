import Game.Metadata
import Game.Support.Randomized

open Game.Randomized

World "RandomizedAlgorithms"
Level 4
Title "Las Vegas Means Always Correct"
-- source: ../game/Game/Worlds/W10Randomized/L04LasVegasCorrect.lean

Introduction "A Las Vegas specification already says every seed in the
experiment produces a correct output. Extract that guarantee for one chosen
seed."

Statement (σ α : Type) (seeds : List σ) (run : σ → α) (good : α → Prop) :
    LasVegas seeds run good → ∀ seed : σ, seed ∈ seeds → good (run seed) := by
  Hint "Unfolding is optional here: the hypothesis is already the function you
  need to apply."
  exact fun h seed hseed => h seed hseed

Conclusion "Las Vegas correctness specializes to each individual seed."

NewDefinition Game.Randomized.LasVegas
