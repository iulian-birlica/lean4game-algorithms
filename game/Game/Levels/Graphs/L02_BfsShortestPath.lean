import Game.Metadata
import Game.Support.Graph

open Game.Graph

World "Graphs"
Level 2
Title "BFS Shortest Path"

Introduction "A BFS layer proof has two parts: a path of length `n`, and a
minimality proof saying every other path has length at least `n`. Package those
two facts as the shortest-path certificate."

Statement {V : Type*} (edge : DirectedGraph V) (source target : V) (n : Nat)
    (hpath : PathLength edge source target n)
    (hmin : ∀ m, PathLength edge source target m → n ≤ m) :
    IsShortest edge source target n := by
  Hint "`IsShortest` is a conjunction. Build it from the path certificate and
  the minimality proof."
  exact ⟨hpath, hmin⟩

Conclusion "The discovered path and layer-minimality proof form a shortest
path certificate."

NewTactic exact
NewDefinition Game.Graph.PathLength Game.Graph.IsShortest
