import Game.Metadata
import Game.Support.Approximation

open Game.Approximation

World "ApproximationAlgorithms"
Level 1
Title "Exact Means One-Approximate"
-- source: ../game/Game/Worlds/W11Approximation/L01ExactIsOneApprox.lean

Introduction "Package feasibility and exact optimal cost as a factor-one
guarantee. Unfold `WithinFactor`: multiplying by `1` changes nothing."

Statement {α : Type} (feasible : α → Prop) (cost : α → ℝ)
    (optimum : ℝ) (candidate : α) :
    feasible candidate →
    cost candidate ≤ optimum →
    WithinFactor feasible cost optimum 1 candidate := by
  Hint "Build the pair: feasibility is one component, and the cost inequality
  becomes the other after a small simplification."
  intro hfeasible hcost
  exact ⟨hfeasible, by simpa using hcost⟩

Conclusion "Exact optimality is a one-approximation guarantee."

NewDefinition Game.Approximation.WithinFactor
NewTactic intro exact simpa
