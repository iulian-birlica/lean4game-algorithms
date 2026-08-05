import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "DataStructures"
Level 1
Title "BST Empty Lookup"

Introduction "A binary search tree threads a dictionary through a plain
binary tree: `lookup` walks left or right by comparing keys. The empty tree
holds nothing, so every lookup into it must fail."

Statement (target : Nat) : SearchTree.lookup target .nil = false := by
  Hint "Unfold `lookup`: matching on the empty tree returns `false` directly,
  with no comparisons to make."
  rfl

Conclusion "Verified: the empty search tree answers every lookup with `false`."

NewTactic rfl
NewDefinition Game.DataStructures.SearchTree Game.DataStructures.SearchTree.nil
  Game.DataStructures.SearchTree.lookup
