import Game.Metadata
import Game.Support.DataStructures

open Game.DataStructures

World "DataStructures"
Level 4
Title "BST Traversal Sortedness"

Introduction "The payoff of the BST invariant: in-order traversal always
produces a sorted list. Split the traversal at the root with
`List.pairwise_append`, and bound each side against the root key using
`forall_mem_inorder_of_all`."

Statement (tree : SearchTree) (h : tree.IsBST) :
    (SearchTree.inorder tree).Pairwise (· < ·) := by
  Hint "In the node case, destructure the BST invariant into its two `All`
  bounds and two sub-invariants. `List.pairwise_append` and
  `List.pairwise_cons` split the goal into the two recursive calls, the
  right-subtree bound, and a cross condition transported through the root
  by `Nat.lt_trans`."
  induction tree with
  | nil => exact List.Pairwise.nil
  | node left key right ih_left ih_right =>
      obtain ⟨hleft_all, hright_all, hleft_bst, hright_bst⟩ := h
      simp only [SearchTree.inorder, List.pairwise_append, List.pairwise_cons, List.mem_cons]
      refine ⟨ih_left hleft_bst,
        ⟨SearchTree.forall_mem_inorder_of_all right hright_all, ih_right hright_bst⟩, ?_⟩
      intro a ha b hb
      rcases hb with hb | hb
      · subst hb
        exact SearchTree.forall_mem_inorder_of_all left hleft_all a ha
      · exact Nat.lt_trans (SearchTree.forall_mem_inorder_of_all left hleft_all a ha)
          (SearchTree.forall_mem_inorder_of_all right hright_all b hb)

Conclusion "Verified: in-order traversal of a binary search tree is sorted."

NewTactic obtain refine rcases
NewDefinition Game.DataStructures.SearchTree.All Game.DataStructures.SearchTree.IsBST
NewTheorem Game.DataStructures.SearchTree.forall_mem_inorder_of_all
  List.pairwise_append List.pairwise_cons List.Pairwise.nil Nat.lt_trans
