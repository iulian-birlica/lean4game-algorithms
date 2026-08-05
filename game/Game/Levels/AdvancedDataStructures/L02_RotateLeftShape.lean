import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "AdvancedDataStructures"
Level 2
Title "Left Rotation Shape"

Introduction "A left rotation is the mirror image of a right rotation: the
right child moves up, and the old root becomes its left child. The displayed
tree is already in the exact shape `rotateLeft` expects."

Statement (a b c : SearchTree) (x y : Nat) :
    AVL.rotateLeft (.node a x (.node b y c)) = .node (.node a x b) y c := by
  Hint "Unfold `rotateLeft` and reduce the matching branch."
  rfl

Conclusion "Verified: `rotateLeft` mirrors the right-rotation shape rule."

NewDefinition Game.DataStructures.AVL.rotateLeft
