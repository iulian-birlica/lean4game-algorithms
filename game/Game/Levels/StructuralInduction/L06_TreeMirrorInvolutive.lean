import Game.Metadata
import Game.Support.Induction

World "StructuralInduction"
Level 6
Title "Tree Mirror Involutive"
-- source: RequestProject Lab02.mirror_mirror

Introduction "Binary trees have a leaf case and a `node` step case with
*two* subtrees, so induction on a tree gives two induction hypotheses.
Start with the structural fact: mirroring twice gives the original tree back."

Statement {α : Type} (t : Game.Induction.Tree α) :
    Game.Induction.Tree.mirror (Game.Induction.Tree.mirror t) = t := by
  Hint "Induct on `t`. In the `node` case you get one induction hypothesis for
  each subtree."
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
    Hint (hidden := true) "Unfold `mirror` twice and rewrite with both induction hypotheses."
    rw [Game.Induction.Tree.mirror, Game.Induction.Tree.mirror, ihl, ihr]

Conclusion "Confirmed: mirroring is an involution."

NewDefinition Game.Induction.Tree Game.Induction.Tree.leaf Game.Induction.Tree.node
  Game.Induction.Tree.mirror
NewTactic ring norm_num simp
NewTheorem Game.Induction.Tree.mirror_mirror
NewTheorem pow_zero le_max_left le_max_right List.length_cons List.length_nil List.Perm.cons
  List.Perm.trans trans Trans.trans Nat.succ_pos symm le_of_lt
