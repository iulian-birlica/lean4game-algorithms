import Game.Metadata
import Game.Support.TableDP

open Game.TableDP

World "TableDynamicProgramming"
Level 7
Title "Floyd-Warshall Layer"

Introduction "A Floyd-Warshall layer allows one more intermediate vertex. Each
updated entry chooses the better of the previous direct distance and the route
through that new intermediate."

/-- One Floyd-Warshall layer is bounded by the direct route and the route through `k`. -/
Statement {V : Type} (previous : V → V → Nat) (k i j : V) :
    floydLayer previous k i j ≤ previous i j ∧
    floydLayer previous k i j ≤ previous i k + previous k j := by
  Hint "Unfold `floydLayer` and `Game.Graph.floydUpdate`; this becomes the
  same minimum argument as the single-update graph level."
  unfold floydLayer Game.Graph.floydUpdate
  exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

Conclusion "Adding a Floyd-Warshall intermediate never makes a distance entry worse."

NewTactic exact unfold
NewDefinition Game.TableDP.floydLayer Game.Graph.floydUpdate
NewTheorem Nat.min_le_left Nat.min_le_right
