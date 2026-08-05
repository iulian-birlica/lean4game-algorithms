import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "DataStructures"
Level 3
Title "BST Lookup Soundness"

Introduction "A successful lookup should be backed by an actual entry.
Turn a `lookup = true` witness into membership in the tree's in-order
traversal, by following the same comparison branch `lookup` took."

Statement (target : Nat) (tree : SearchTree) :
    SearchTree.lookup target tree = true → target ∈ SearchTree.inorder tree := by
  Hint "Induct on the tree. The empty case is vacuous, since lookup there is
  always `false`. In the node case, unfold `lookup` and `inorder`, then split
  on the same two comparisons; the third branch forces `target = key` by
  `omega`."
  induction tree with
  | nil => intro h; simp [SearchTree.lookup] at h
  | node left key right ih_left ih_right =>
      unfold SearchTree.lookup
      simp only [SearchTree.inorder]
      split_ifs with h1 h2
      · intro h
        exact List.mem_append.mpr (Or.inl (ih_left h))
      · intro h
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (ih_right h))))
      · intro _
        have hkey : target = key := by omega
        subst hkey
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

Conclusion "Verified: every successful lookup certifies an in-order membership."

NewTactic intro exact subst omega
NewDefinition Game.DataStructures.SearchTree.inorder
NewTheorem List.mem_append List.mem_cons
