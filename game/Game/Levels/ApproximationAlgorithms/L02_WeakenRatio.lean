import Game.Metadata
import Game.Support.Approximation

open Game.Approximation

World "ApproximationAlgorithms"
Level 2
Title "Weaken an Approximation Ratio"
-- source: ../game/Game/Worlds/W11Approximation/L02WeakenRatio.lean

Introduction "A bound that is good enough for ratio `small` is also good
enough for any larger ratio `large`, provided the optimum is nonnegative."

Statement {α : Type} (feasible : α → Prop) (cost : α → ℝ)
    (optimum small large : ℝ) (candidate : α) :
    0 ≤ optimum →
    small ≤ large →
    WithinFactor feasible cost optimum small candidate →
    WithinFactor feasible cost optimum large candidate := by
  Hint "Keep the feasibility half. For the cost half, compare
  `small * optimum` and `large * optimum` using `0 ≤ optimum`."
  intro hoptimum hfactor happrox
  exact ⟨happrox.1, by nlinarith [happrox.2]⟩

Conclusion "Approximation ratios can be weakened monotonically."

NewTactic intro exact nlinarith
