import Game.Metadata
import Game.Support.Approximation

open Game.Approximation

World "ApproximationAlgorithms"
Level 5
Title "Take Both Endpoints"
-- source: ../game/Game/Worlds/W11Approximation/L05EndpointAccounting.lean

Introduction "The maximal-matching vertex-cover algorithm selects at most
two endpoints per matching edge. Recover that accounting inequality from the
certificate."

Statement (graph : Game.Complexity.FiniteGraph)
    (cert : VertexCoverCertificate graph) :
    (cert.cover.card : ℝ) ≤ 2 * cert.matchingSize := by
  Hint "Read the certificate fields literally."
  exact cert.endpointAccounting

Conclusion "The endpoint accounting step is available."

NewTactic intro exact
