import Game.Metadata
import Game.Support.Graph

open Game.Graph

World "Graphs"
Level 6
Title "Strongly Connected Components"

Introduction "For directed graphs, strongly connected vertices are mutually
reachable. Prove that this mutual-reachability relation is reflexive,
symmetric, and transitive."

Statement {V : Type*} (edge : DirectedGraph V) :
    Equivalence (StronglyConnected edge) := by
  Hint "For transitivity, compose the forward paths and compose the reverse
  paths in the opposite order."
  have reach_trans : ∀ {u v w : V}, Reach edge u v → Reach edge v w → Reach edge u w := by
    intro u v w huv hvw
    induction hvw with
    | refl => exact huv
    | tail h e ih => exact Reach.tail ih e
  constructor
  · intro x
    exact ⟨Reach.refl, Reach.refl⟩
  · intro x y hxy
    exact ⟨hxy.2, hxy.1⟩
  · intro x y z hxy hyz
    exact ⟨reach_trans hxy.1 hyz.1, reach_trans hyz.2 hxy.2⟩

Conclusion "Strong connectivity is an equivalence relation."

NewTactic intro induction constructor exact
NewDefinition Game.Graph.DirectedGraph Game.Graph.Reach Game.Graph.StronglyConnected
NewTheorem Game.Graph.Reach.refl Game.Graph.Reach.tail
