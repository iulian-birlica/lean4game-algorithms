import Game.Metadata
import Game.Support.PrefixStrings

open Game.String

World "PrefixStrings"
Level 2
Title "Common Prefix Match Step"

Introduction "When both lists start with the same symbol, that symbol
contributes one more to the common-prefix length, and the rest of the
measurement continues on the tails."

Statement {α : Type} [DecidableEq α] (x : α) (xs ys : List α) :
    commonPrefixLength (x :: xs) (x :: ys) = commonPrefixLength xs ys + 1 := by
  Hint "Matching leading symbols take the `if`'s true branch."
  exact if_pos rfl

Conclusion "A matching head always extends the common prefix by one."
