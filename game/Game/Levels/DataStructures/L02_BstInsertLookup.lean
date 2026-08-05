import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "DataStructures"
Level 2
Title "BST Insert Lookup"

Introduction "`insert` walks down the same comparisons as `lookup`, so a key
is always immediately findable right after it is inserted. Induct on the
tree and split on where the new key lands relative to each root."

Statement (target : Nat) (tree : SearchTree) :
    SearchTree.lookup target (SearchTree.insert target tree) = true := by
  Hint "In the empty case, `insert` creates a fresh root equal to `target`,
  and comparing a key against itself never satisfies `<`. In the node case,
  first unfold `insert` and split on its two comparisons, so each branch's
  tree shape is concrete; only then does unfolding `lookup` there expose the
  matching comparison to close with the same split facts."
  induction tree with
  | nil => simp [SearchTree.insert, SearchTree.lookup]
  | node left key right ih_left ih_right =>
      unfold SearchTree.insert
      split_ifs with h1 h2
      · simp [SearchTree.lookup, h1, ih_left]
      · simp [SearchTree.lookup, h1, h2, ih_right]
      · simp [SearchTree.lookup, h1, h2]

Conclusion "Verified: a key inserted into a search tree is immediately found by lookup."

NewTactic induction simp unfold split_ifs
NewDefinition Game.DataStructures.SearchTree.node Game.DataStructures.SearchTree.insert
