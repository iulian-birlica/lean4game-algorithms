import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "AdvancedDataStructures"
Level 3
Title "Right Left Round Trip"

Introduction "If a tree is in the exact shape for a right rotation, then
rotating right and immediately rotating left should return to the original
tree."

Statement (a b c : SearchTree) (x y : Nat) :
    AVL.rotateLeft (AVL.rotateRight (.node (.node a x b) y c)) =
      .node (.node a x b) y c := by
  Hint "Use the concrete shape lemmas hidden inside the definitions: after
  `rotateRight` simplifies, `rotateLeft` matches its own rotation branch."
  rfl

Conclusion "A left rotation undoes this right rotation on the displayed shape."
