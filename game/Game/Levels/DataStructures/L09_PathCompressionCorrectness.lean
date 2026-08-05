import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "DataStructures"
Level 9
Title "Path Compression Correctness"

Introduction "Union-find speeds up future queries by compressing a parent
pointer directly to its class representative. That optimization must be
invisible to every abstract representative: compressing never changes what
`representative` reports, since `compress` keeps that field unchanged."

Statement {V : Type} [DecidableEq V] (set : DisjointSet V) (x y : V) :
    (set.compress x).representative y = set.representative y := by
  Hint "`compress` reuses `set.representative` verbatim as its own
  `representative` field, so this holds definitionally."
  rfl

Conclusion "Verified: path compression preserves every abstract representative."

NewDefinition Game.DataStructures.DisjointSet Game.DataStructures.DisjointSet.compress
