import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "AdvancedDataStructures"
Level 6
Title "Left Rotation Preserves Inorder"

Introduction "The mirror-image rotation should preserve the same in-order
traversal for the same reason: keys move between parent and child positions,
but their left-to-right order stays fixed."

Statement (a b c : SearchTree) (x y : Nat) :
    SearchTree.inorder (AVL.rotateLeft (.node a x (.node b y c))) =
      SearchTree.inorder (.node a x (.node b y c)) := by
  Hint "Unfold `rotateLeft` and `inorder`, then reassociate the appended
  lists."
  simp [AVL.rotateLeft, SearchTree.inorder, List.append_assoc]

Conclusion "Verified: left rotation also preserves in-order traversal."
