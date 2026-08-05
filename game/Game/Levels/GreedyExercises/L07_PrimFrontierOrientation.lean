import Game.Metadata
import Game.Support.GreedyExercises

open Game.Greedy

World "GreedyExercises"
Level 7
Title "Prim Frontier Orientation"

Introduction "Prim's algorithm grows a visited set and considers frontier edges.
If `u` is already inside the set and `v` is outside, then the edge from `u` to
`v` crosses the cut in the forward orientation."

/-- An edge from inside the visited set to outside it crosses the cut. -/
Statement {V : Type} (left : Set V) (u v : V)
    (hu : u ∈ left) (hv : v ∉ left) :
    Game.Graph.CrossesCut left u v := by
  Hint "`CrossesCut` is an `Or`; choose the orientation matching `u ∈ left`
  and `v ∉ left`."
  exact Or.inl ⟨hu, hv⟩

Conclusion "The frontier edge is oriented as a cut-crossing edge."

NewTactic exact
NewDefinition Game.Graph.CrossesCut Or.inl
