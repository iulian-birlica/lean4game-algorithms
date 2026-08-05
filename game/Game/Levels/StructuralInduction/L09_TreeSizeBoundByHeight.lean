import Game.Metadata
import Game.Support.Induction

World "StructuralInduction"
Level 9
Title "Tree Size Bound by Height"
-- source: RequestProject Lab02.size_lt_two_pow_height

Introduction "A quantitative induction: a tree of height `h` has fewer than
`2 ^ h` nodes. Bound each subtree by `2 ^ height`, combine, and let `omega`
finish the arithmetic."

Statement {α : Type} (t : Game.Induction.Tree α) :
    Game.Induction.Tree.size t < 2 ^ Game.Induction.Tree.height t := by
  Hint "Induct on `t`. The leaf case is immediate; the step case bounds each
  subtree's size by `2 ^ max (height l) (height r)`."
  induction t with
  | leaf => rw [Game.Induction.Tree.size, Game.Induction.Tree.height, pow_zero]; omega
  | node l x r ihl ihr =>
    rw [Game.Induction.Tree.size, Game.Induction.Tree.height]
    Hint (hidden := true) "Bound both subtrees' `2 ^ height` by `2 ^ max ...` using
    `Nat.pow_le_pow_right` and `le_max_left`/`le_max_right`, expand `2 ^ (n+1)`
    with `ring`, then `omega`."
    have hl : (2 : Nat) ^ Game.Induction.Tree.height l
        ≤ 2 ^ max (Game.Induction.Tree.height l) (Game.Induction.Tree.height r) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have hr : (2 : Nat) ^ Game.Induction.Tree.height r
        ≤ 2 ^ max (Game.Induction.Tree.height l) (Game.Induction.Tree.height r) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    have hpow : (2 : Nat) ^ (max (Game.Induction.Tree.height l) (Game.Induction.Tree.height r) + 1)
        = 2 ^ max (Game.Induction.Tree.height l) (Game.Induction.Tree.height r)
          + 2 ^ max (Game.Induction.Tree.height l) (Game.Induction.Tree.height r) := by ring
    omega

Conclusion "Bounded: a tree's node count never reaches `2 ^ height`."

NewDefinition Game.Induction.Tree.height Nat Max.max
NewTheorem Nat.pow_le_pow_right
