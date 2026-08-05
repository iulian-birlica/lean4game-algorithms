import Game.Metadata
import Game.Support.Graph

open Game.Graph

World "Graphs"
Level 1
Title "BFS Queue Invariant"

Introduction "A breadth-first search queue should contain only vertices that
have already been discovered from the source. If the old queue satisfies that
invariant, and every new neighbor is reached by one edge from a reached vertex,
then appending those neighbors preserves the invariant."

Statement {V : Type*} (edge : DirectedGraph V) (source u : V) (queue neighbors : List V)
    (hq : QueueInvariant edge source queue) (hu : Reach edge source u)
    (hneighbors : ∀ v ∈ neighbors, edge u v) :
    QueueInvariant edge source (queue ++ neighbors) := by
  Hint "Unfold the queue invariant by introducing a vertex and its membership
  proof. Then split membership in an appended list with `List.mem_append`."
  intro v hv
  rcases List.mem_append.mp hv with hv_queue | hv_neighbors
  · exact hq v hv_queue
  · exact Reach.tail hu (hneighbors v hv_neighbors)

Conclusion "Appending newly discovered neighbors preserves the BFS queue
invariant."

NewTactic intro rcases exact
NewDefinition Game.Graph.DirectedGraph Game.Graph.QueueInvariant Game.Graph.Reach
NewTheorem List.mem_append Game.Graph.Reach.tail
