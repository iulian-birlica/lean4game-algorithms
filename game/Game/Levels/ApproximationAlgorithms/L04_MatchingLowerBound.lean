import Game.Metadata
import Game.Support.Approximation

open Game.Approximation

World "ApproximationAlgorithms"
Level 4
Title "Matching Lower Bound"
-- source: ../game/Game/Worlds/W11Approximation/L04MatchingLowerBound.lean

Introduction "A disjoint matching certifies a lower bound for every vertex
cover: each matching edge forces the cover to pay at least one endpoint."

Statement (graph : Game.Complexity.FiniteGraph)
    (cert : VertexCoverCertificate graph) (candidate : Finset graph.vertices) :
    graph.VertexCover candidate →
    (cert.matchingSize : ℝ) ≤ candidate.card := by
  Hint "This is one of the fields already stored in the certificate."
  intro hcandidate
  exact cert.matchingLowerBound candidate hcandidate

Conclusion "The matching lower bound is extracted from the certificate."

NewDefinition Game.Approximation.VertexCoverCertificate
NewTactic intro exact
