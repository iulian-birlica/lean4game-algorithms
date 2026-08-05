import Game.Metadata
import Game.Support.Graph

open Game.Graph

World "Graphs"
Level 5
Title "Connected Components"

Introduction "In an undirected graph, reachability is an equivalence relation:
every vertex reaches itself, paths can be reversed, and paths can be
concatenated. These are the facts behind connected components."

Statement {V : Type*} (edge : DirectedGraph V) (hsym : Symmetric edge) :
    Equivalence (fun u v => Reach edge u v) := by
  Hint "First prove transitivity by induction on the second reachability proof.
  Then use edge symmetry to reverse paths."
  have reach_trans : ∀ {u v w : V}, Reach edge u v → Reach edge v w → Reach edge u w := by
    intro u v w huv hvw
    induction hvw with
    | refl => exact huv
    | tail h e ih => exact Reach.tail ih e
  have reach_symm : ∀ {u v : V}, Reach edge u v → Reach edge v u := by
    intro u v huv
    induction huv with
    | refl => exact Reach.refl
    | tail h e ih =>
        exact reach_trans (Reach.tail Reach.refl (hsym e)) ih
  constructor
  · intro u
    exact Reach.refl
  · intro u v huv
    exact reach_symm huv
  · intro u v w huv hvw
    exact reach_trans huv hvw

Conclusion "Undirected reachability forms the connected-component equivalence
relation."

NewTactic intro induction constructor exact
NewDefinition Game.Graph.DirectedGraph Game.Graph.Reach
NewTheorem Game.Graph.Reach.refl Game.Graph.Reach.tail
