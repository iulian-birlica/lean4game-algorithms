import Game.Metadata
import Game.Support.Graph

open Game.Graph

World "Graphs"
Level 9
Title "Floyd-Warshall Update"

Introduction "A Floyd-Warshall table update chooses the better of the direct
route and the route through the current intermediate vertex. That updated value
is bounded by both candidates."

Statement (direct viaLeft viaRight : Nat) :
    floydUpdate direct viaLeft viaRight ≤ direct ∧
    floydUpdate direct viaLeft viaRight ≤ viaLeft + viaRight := by
  Hint "`floydUpdate` is a minimum. Prove the two projections with the two
  `Nat.min_le_*` lemmas."
  exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

Conclusion "The Floyd-Warshall update is no worse than either available route."

NewTactic exact
NewDefinition Game.Graph.floydUpdate
NewTheorem Nat.min_le_left Nat.min_le_right
