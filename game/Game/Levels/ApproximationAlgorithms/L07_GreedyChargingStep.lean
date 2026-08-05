import Game.Metadata
import Game.Support.Approximation

open Game.Approximation

World "ApproximationAlgorithms"
Level 7
Title "One Greedy Set-Cover Charge"
-- source: ../game/Game/Worlds/W11Approximation/L07GreedyChargingStep.lean

Introduction "Unfold one step of the greedy set-cover charging recurrence:
the next stage contributes exactly `optimum / (n + 1)`."

Statement (optimum : ℝ) (n : Nat) :
    greedySetCoverBound optimum (n + 1) =
      greedySetCoverBound optimum n + optimum / (n + 1) := by
  Hint "This is the successor clause in the definition."
  rfl

Conclusion "The charging recurrence is exposed one step at a time."

NewDefinition Game.Approximation.greedySetCoverBound
