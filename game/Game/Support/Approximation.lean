import Game.Support.Complexity
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Answer-free definitions used by the approximation-algorithms world. Ported
from the older game tree and adapted to the current project layout. -/
namespace Game.Approximation

/-- A feasible candidate is within factor `factor` of a minimization
optimum. -/
def WithinFactor {α : Type} (feasible : α → Prop) (cost : α → ℝ)
    (optimum factor : ℝ) (candidate : α) : Prop :=
  feasible candidate ∧ cost candidate ≤ factor * optimum

/-- A certificate emitted by the maximal-matching vertex-cover algorithm.
`matchingSize` is a lower bound because every cover must meet every disjoint
matching edge; the algorithm takes at most both endpoints of each matching
edge. -/
structure VertexCoverCertificate (graph : Game.Complexity.FiniteGraph) where
  cover : Finset graph.vertices
  matchingSize : Nat
  isCover : graph.VertexCover cover
  matchingLowerBound : ∀ candidate, graph.VertexCover candidate →
    (matchingSize : ℝ) ≤ candidate.card
  endpointAccounting : (cover.card : ℝ) ≤ 2 * matchingSize

/-- The harmonic charging recurrence for greedy set cover. At stage `n + 1`,
greedy charges at most `OPT / (n + 1)` before continuing with `n` uncovered
elements. -/
noncomputable def greedySetCoverBound (optimum : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => greedySetCoverBound optimum n + optimum / (n + 1)

/-- A completed greedy set-cover run, with feasibility and its charging
bound. -/
structure SetCoverCertificate (α : Type) (feasible : α → Prop) (cost : α → ℝ) where
  chosen : α
  initialUncovered : Nat
  costOptimum : ℝ
  isFeasible : feasible chosen
  chargingBound : cost chosen ≤ greedySetCoverBound costOptimum initialUncovered
  optimum_nonneg : 0 ≤ costOptimum

/-- The accounting data in the double-tree algorithm for metric TSP. The MST
is no more expensive than an optimal tour; doubling it gives a closed walk;
metric shortcutting turns that walk into a tour without increasing cost. -/
structure MetricTSPCertificate (Tour : Type) (feasible : Tour → Prop) (cost : Tour → ℝ) where
  tour : Tour
  optimum : ℝ
  mstCost : ℝ
  doubledWalkCost : ℝ
  isTour : feasible tour
  optimum_nonneg : 0 ≤ optimum
  mstLowerBound : mstCost ≤ optimum
  doubledTreeBound : doubledWalkCost ≤ 2 * mstCost
  shortcutBound : cost tour ≤ doubledWalkCost

end Game.Approximation
