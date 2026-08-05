import Game.Metadata
import Game.Support.Induction

World "StructuralInduction"
Level 2
Title "List Append Length"
-- source: RequestProject Lab02.len_app

Introduction "Now prove that append also behaves correctly with `len`:
the length of `append xs ys` is the sum of the two lengths."

Statement {α : Type} (xs ys : Game.Induction.List α) :
    Game.Induction.List.len (Game.Induction.List.append xs ys)
      = Game.Induction.List.len xs + Game.Induction.List.len ys := by
  Hint "Induct on `xs`."
  induction xs with
  | nil =>
    Hint (hidden := true) "Unfold `append` and `len`, then use `Nat.zero_add`."
    rw [Game.Induction.List.append, Game.Induction.List.len, Nat.zero_add]
  | cons x xs ih =>
    Hint (hidden := true) "Unfold `append` and `len`, rewrite with the induction hypothesis, then finish the arithmetic."
    rw [Game.Induction.List.append, Game.Induction.List.len, Game.Induction.List.len, ih]
    omega

Conclusion "Verified: append adds lengths."

NewTactic omega
NewDefinition Game.Induction.List.len
NewTheorem Nat.zero_add Game.Induction.List.len_append
