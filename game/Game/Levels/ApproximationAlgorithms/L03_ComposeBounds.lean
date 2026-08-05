import Game.Metadata
import Game.Support.Approximation

open Game.Approximation

World "ApproximationAlgorithms"
Level 3
Title "Compose Approximation Bounds"
-- source: ../game/Game/Worlds/W11Approximation/L03ComposeBounds.lean

Introduction "Compose an algorithm-to-proxy factor with a
proxy-to-optimum factor. The inequalities chain once you multiply by the
nonnegative first factor."

Statement {α : Type} (feasible : α → Prop) (cost : α → ℝ)
    (candidate : α) (proxy optimum first second : ℝ) :
    feasible candidate →
    0 ≤ first →
    cost candidate ≤ first * proxy →
    proxy ≤ second * optimum →
    WithinFactor feasible cost optimum (first * second) candidate := by
  Hint "The feasibility half is immediate. For the cost half, multiply the
  proxy bound by `first` and combine it with the cost bound."
  intro hfeasible hfirst hcost hproxy
  constructor
  · exact hfeasible
  · nlinarith

Conclusion "Two approximation steps compose into one."

NewTactic intro constructor exact nlinarith
