import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "AdvancedDataStructures"
Level 5
Title "Right Rotation Preserves Inorder"

Introduction "A rotation should preserve the sorted key sequence seen by
in-order traversal. For the right rotation, both sides should flatten to the
same list of keys."

Statement (a b c : SearchTree) (x y : Nat) :
    SearchTree.inorder (AVL.rotateRight (.node (.node a x b) y c)) =
      SearchTree.inorder (.node (.node a x b) y c) := by
  Hint "Unfold `rotateRight` and `inorder`, then simplify the list
  concatenations."
  simp [AVL.rotateRight, SearchTree.inorder, List.append_assoc]

Conclusion "Verified: the rotation changes tree shape, not in-order content."

NewDefinition Game.DataStructures.SearchTree.inorder
