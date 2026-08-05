import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "DataStructures"
Level 5
Title "AVL Singleton"

Introduction "An AVL tree is a search tree with a height-balance guarantee
on top. The smallest nontrivial case, a single key with two empty
subtrees, certifies both conditions at once: it is trivially ordered, and
both subtrees share height `0`."

Statement (key : Nat) : AVL.IsAVL (.node .nil key .nil) := by
  Hint "Unfold `IsAVL`, `IsBST`, `All`, `Balanced`, and `height`; every
  remaining fact is either `True` or a comparison against `0`."
  simp +decide [AVL.IsAVL, AVL.Balanced, AVL.height, SearchTree.IsBST, SearchTree.All]

Conclusion "Verified: a singleton search tree is an AVL tree."

NewDefinition Game.DataStructures.AVL.IsAVL Game.DataStructures.AVL.Balanced
  Game.DataStructures.AVL.height
