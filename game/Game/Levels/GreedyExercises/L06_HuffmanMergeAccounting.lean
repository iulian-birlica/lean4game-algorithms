import Game.Metadata
import Game.Support.GreedyExercises

open Game.Greedy

World "GreedyExercises"
Level 6
Title "Huffman Merge Accounting"

Introduction "Merging two Huffman subtrees pushes every old leaf one level
deeper. First prove the reusable accounting fact: increasing the starting depth
by one adds exactly the total weight of the tree."

/-- Merging two Huffman trees adds both subtree weights to the external cost. -/
Statement (left right : HuffmanTree) :
    (HuffmanTree.node left right).externalCost 0 =
      left.externalCost 0 + right.externalCost 0 + left.weight + right.weight := by
  Hint "`HuffmanTree.externalCost_succ` says that pushing every leaf one level
  deeper adds the total subtree weight."
  simp [HuffmanTree.externalCost, HuffmanTree.externalCost_succ]
  ring

Conclusion "The cost of a Huffman merge is the old external cost plus the weight of both subtrees."

NewTactic ring simp
NewDefinition Game.Greedy.HuffmanTree.externalCost Game.Greedy.HuffmanTree.weight
NewTheorem Game.Greedy.HuffmanTree.externalCost_succ
