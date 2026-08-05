import Game.Metadata
import Game.Support.Approximation

open Game.Approximation

World "ApproximationAlgorithms"
Level 6
Title "Vertex Cover Two-Approximation"
-- source: ../game/Game/Worlds/W11Approximation/L06VertexCoverTwoApprox.lean

Introduction "Combine the matching lower bound with the endpoint accounting
bound to certify the standard factor-`2` approximation for vertex cover."

Statement (graph : Game.Complexity.FiniteGraph)
    (cert : VertexCoverCertificate graph) (optimum : ℝ) :
    (cert.matchingSize : ℝ) ≤ optimum →
    WithinFactor graph.VertexCover (fun cover => (cover.card : ℝ))
      optimum 2 cert.cover := by
  Hint "Use `cert.isCover` for feasibility, then compare
  `cover.card ≤ 2 * matchingSize ≤ 2 * optimum`."
  intro hmatch
  exact ⟨cert.isCover, by linarith [hmatch, cert.endpointAccounting]⟩

Conclusion "The matching-based algorithm is certified as a two-approximation."

NewTactic intro exact linarith
