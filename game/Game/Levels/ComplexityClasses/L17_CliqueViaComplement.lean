import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 17
Title "Cliques via Complement"
-- source: ../game/Game/Worlds/W07Complexity/L08CliqueIndependent.lean

Introduction "A clique in a graph is exactly an independent set in the **complement** graph:
adjacency inside the clique becomes non-adjacency after complementing."

Statement (graph : FiniteGraph) (set : Finset graph.vertices) :
    graph.Clique set ↔ graph.complement.Independent set := by
  Hint "Unfold both predicates and the complement edge relation."
  constructor
  · intro h u hu v hv hedge
    exact hedge.2 (h hu hv hedge.1)
  · intro h u hu v hv huv
    by_contra hedge
    exact h hu hv ⟨huv, hedge⟩

Conclusion "Verified: cliques are independent sets in the complement graph."

NewDefinition Game.Complexity.FiniteGraph Game.Complexity.FiniteGraph.Independent
  Game.Complexity.FiniteGraph.Clique Game.Complexity.FiniteGraph.complement
