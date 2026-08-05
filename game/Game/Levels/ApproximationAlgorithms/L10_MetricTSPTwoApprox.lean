import Game.Metadata
import Game.Support.Approximation

open Game.Approximation

World "ApproximationAlgorithms"
Level 10
Title "Metric TSP Two-Approximation"
-- source: ../game/Game/Worlds/W11Approximation/L10MetricTSPTwoApprox.lean

Introduction "Assemble the MST lower bound, the doubled-tree upper bound,
and the shortcutting inequality to recover the standard metric-TSP
two-approximation."

Statement {Tour : Type} (feasible : Tour → Prop) (cost : Tour → ℝ)
    (cert : MetricTSPCertificate Tour feasible cost) :
    WithinFactor feasible cost cert.optimum 2 cert.tour := by
  Hint "Use the certificate's feasibility field, then chain
  `tour ≤ doubled walk ≤ 2 * MST ≤ 2 * optimum`."
  constructor
  · exact cert.isTour
  · linarith [cert.shortcutBound, cert.doubledTreeBound, cert.mstLowerBound]

Conclusion "The double-tree metric-TSP analysis is assembled."

NewDefinition Game.Approximation.MetricTSPCertificate
NewTactic constructor exact linarith
