import Game.Metadata
import Game.Support.Graph

open Game.Graph

World "Graphs"
Level 10
Title "Minimum Spanning Tree Cut"

Introduction "Prim's and Kruskal's algorithms rely on the cut property: a light
edge crossing a cut is no heavier than any other edge crossing that cut. Extract
that comparison from the definition."

Statement {V : Type*} (weight : V → V → Nat) (left : Set V) (u v x y : V)
    (hlight : IsLightCutEdge weight left u v) (hcross : CrossesCut left x y) :
    weight u v ≤ weight x y := by
  Hint "`IsLightCutEdge` is a pair: first the chosen edge crosses the cut, then
  it is no heavier than every crossing edge."
  exact hlight.2 x y hcross

Conclusion "A light cut edge is bounded by every other crossing edge."

NewTactic exact
NewDefinition Game.Graph.CrossesCut Game.Graph.IsLightCutEdge
