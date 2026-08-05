import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L01_Asymptotics

open Game.Clockwork

World "Asymptotics"
Level 2
Title "The Power n^1"

Introduction "Before comparing growth rates, it helps to know what the
reference power function `rpol` does in easy cases. At exponent `1`, it is
just the linear function `n ↦ n`."

/-- The reference power function at exponent `1` is the identity. -/
Statement rpol_one (n : ℕ) : rpol 1 n = n := by
  Hint "Unfold `rpol`: raising to the first power changes nothing."
  norm_num [rpol]

Conclusion "The notation `rpol 1` is just another name for linear growth."

NewDefinition Game.Clockwork.rpol
NewTheorem rpol_one
