import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "AdvancedDataStructures"
Level 1
Title "Right Rotation Shape"

Introduction "A right rotation promotes the left child of a node and demotes
the old root to the right. On the concrete tree shown in the statement,
`rotateRight` should reduce to exactly that rearrangement."

Statement (a b c : SearchTree) (x y : Nat) :
    AVL.rotateRight (.node (.node a x b) y c) = .node a x (.node b y c) := by
  Hint "Unfold `rotateRight`: this input already matches the rotation branch,
  so no further case split is needed."
  rfl

Conclusion "Verified: `rotateRight` performs the expected local reshaping."

NewDefinition Game.DataStructures.AVL.rotateRight
