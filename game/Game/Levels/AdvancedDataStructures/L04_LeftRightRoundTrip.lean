import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "AdvancedDataStructures"
Level 4
Title "Left Right Round Trip"

Introduction "The mirrored statement should also hold: on a tree already in
left-rotation shape, rotating left and then right returns to the starting
tree."

Statement (a b c : SearchTree) (x y : Nat) :
    AVL.rotateRight (AVL.rotateLeft (.node a x (.node b y c))) =
      .node a x (.node b y c) := by
  Hint "As in the previous level, both rotations immediately reduce on this
  concrete tree."
  rfl

Conclusion "The displayed left rotation is reversed by an immediate right rotation."
