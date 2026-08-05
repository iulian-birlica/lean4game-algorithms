import Game.Metadata
import Game.Support.Graph

open Game.Graph

World "Graphs"
Level 3
Title "DFS Reachability"

Introduction "Depth-first search grows a reachability certificate one edge at a
time. If `u` has already been reached from the source and there is an edge from
`u` to `v`, then `v` is reached as well."

Statement {V : Type*} (edge : DirectedGraph V) (source u v : V)
    (hu : Reach edge source u) (huv : edge u v) : Reach edge source v := by
  Hint "Use the constructor that extends reachability across one tail edge."
  exact Reach.tail hu huv

Conclusion "Reachability extends across each DFS tree or back edge."

NewTactic exact
NewDefinition Game.Graph.DirectedGraph Game.Graph.Reach
NewTheorem Game.Graph.Reach.tail
