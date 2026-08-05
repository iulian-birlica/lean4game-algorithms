import Game.Metadata
import Game.Support.Graph

open Game.Graph

World "Graphs"
Level 4
Title "Topological Order"

Introduction "A topological order is exactly the invariant that every listed
edge points forward. Read that invariant to recover the index comparison for a
particular edge."

Statement {V : Type*} [BEq V] (edge : DirectedGraph V) (order : List V)
    (horder : IsTopological edge order) {u v : V}
    (hu : u ∈ order) (hv : v ∈ order) (huv : edge u v) :
    order.idxOf u < order.idxOf v := by
  Hint "`IsTopological` is already the statement you need, specialized to
  these two vertices."
  exact horder hu hv huv

Conclusion "The topological-order invariant gives the forward edge direction."

NewTactic exact
NewDefinition Game.Graph.DirectedGraph Game.Graph.IsTopological
