import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "AdvancedDataStructures"
Level 7
Title "Right Rotation Preserves Lookup"

Introduction "Lookup follows comparisons, not tree shape alone. For the
displayed right rotation, the promoted key `x` must stay below the demoted key
`y`; under that ordering assumption, `lookup` should make the same decision on
either tree."

Statement (a b c : SearchTree) (x y target : Nat) (hxy : x < y) :
    SearchTree.lookup target (AVL.rotateRight (.node (.node a x b) y c)) =
      SearchTree.lookup target (.node (.node a x b) y c) := by
  Hint "Unfold `rotateRight` and `lookup`, simplify the comparisons, then let
  arithmetic close the remaining target-vs-key cases."
  unfold AVL.rotateRight
  simp +arith +decide [SearchTree.lookup]
  grind

Conclusion "Verified: this rotation preserves lookup outcomes."

NewDefinition Game.DataStructures.SearchTree.lookup
