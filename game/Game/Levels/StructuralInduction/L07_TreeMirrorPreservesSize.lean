import Game.Metadata
import Game.Support.Induction

World "StructuralInduction"
Level 7
Title "Tree Mirror Preserves Size"
-- source: RequestProject Lab02.size_mirror

Introduction "Now keep the same tree-induction shape, but track a quantity:
mirroring should not change how many nodes the tree has."

Statement {α : Type} (t : Game.Induction.Tree α) :
    Game.Induction.Tree.size (Game.Induction.Tree.mirror t) = Game.Induction.Tree.size t := by
  Hint "Induct on `t`. The `node` case again gives hypotheses `ihl` and `ihr`
  for the left and right subtrees."
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
    Hint (hidden := true) "Unfold `mirror` and `size` on both sides, rewrite with `ihl` and `ihr`, then finish the arithmetic."
    rw [Game.Induction.Tree.mirror, Game.Induction.Tree.size, Game.Induction.Tree.size, ihl, ihr]
    omega

Conclusion "Confirmed: mirroring keeps the node count unchanged."

NewDefinition Game.Induction.Tree.size
NewTheorem Game.Induction.Tree.size_mirror
