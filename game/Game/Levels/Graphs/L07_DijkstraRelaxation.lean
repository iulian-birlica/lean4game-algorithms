import Game.Metadata
import Game.Support.Graph

open Game.Graph

World "Graphs"
Level 7
Title "Dijkstra Relaxation"

Introduction "A relaxation replaces the current tentative distance with the
minimum of the old distance and the route through one more edge. Therefore it
is no larger than either candidate."

Statement (du dv weight : Nat) :
    relax du dv weight ≤ dv ∧ relax du dv weight ≤ du + weight := by
  Hint "Unfolding is optional: `relax` is a `min`, and `Nat.min_le_left` /
  `Nat.min_le_right` prove the two sides."
  exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

Conclusion "Relaxation never increases beyond either available route."

NewTactic exact
NewDefinition Game.Graph.relax
NewTheorem Nat.min_le_left Nat.min_le_right
