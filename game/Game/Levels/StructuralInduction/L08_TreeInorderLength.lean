import Game.Metadata
import Game.Support.Induction

World "StructuralInduction"
Level 8
Title "Tree Inorder Length"
-- source: RequestProject Lab02.len_inorder

Introduction "The in-order traversal of a tree should have exactly one
entry per node. Prove it — the step case needs the `len_append` card from
List Append Length."

Statement {α : Type} (t : Game.Induction.Tree α) :
    Game.Induction.List.len (Game.Induction.Tree.inorder t) = Game.Induction.Tree.size t := by
  Hint "Induct on `t`; unfold `inorder` and use `len_append` in the step case."
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
    Hint (hidden := true) "`rw [inorder, len_append, ihl, len, ihr, size]`, then `omega`."
    rw [Game.Induction.Tree.inorder, Game.Induction.List.len_append, ihl, Game.Induction.List.len,
      ihr, Game.Induction.Tree.size]
    omega

Conclusion "Counted: the in-order traversal has one entry per node."

NewDefinition Game.Induction.Tree.inorder
