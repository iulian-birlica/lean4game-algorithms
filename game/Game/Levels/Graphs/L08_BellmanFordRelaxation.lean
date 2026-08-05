import Game.Metadata
import Game.Support.Graph

open Game.Graph

World "Graphs"
Level 8
Title "Bellman-Ford Relaxation"

Introduction "Bellman-Ford repeatedly applies the same local relaxation. If a
bound already covers either the old distance or the newly proposed distance,
then it also covers the relaxed distance."

Statement (du dv weight bound : Nat)
    (hbound : dv ≤ bound ∨ du + weight ≤ bound) :
    relax du dv weight ≤ bound := by
  Hint "Unfold `relax`; the goal becomes a fact about `min` and the disjunctive
  bound."
  unfold relax
  omega

Conclusion "Relaxation preserves a common upper bound."

NewTactic unfold omega
NewDefinition Game.Graph.relax
