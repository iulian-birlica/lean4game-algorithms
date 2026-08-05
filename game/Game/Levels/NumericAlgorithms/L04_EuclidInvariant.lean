import Game.Metadata
import Game.Support.Numeric

open Game.Numeric

World "NumericAlgorithms"
Level 4
Title "Euclid's Remainder Invariant"
-- source: ../game/Game/Worlds/W12Numeric/L04EuclidInvariant.lean

Introduction "Euclid's algorithm replaces `(a, b)` by `(b, a % b)` without
changing the gcd. Prove that standard remainder recurrence."

Statement (a b : Nat) :
    Nat.gcd a b = Nat.gcd b (a % b) := by
  Hint "Rewrite with `Nat.gcd_rec`, taking care of the commuted argument
  order."
  rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]

Conclusion "The gcd survives one Euclidean remainder step."

NewTactic rw
NewTheorem Nat.gcd_comm Nat.gcd_rec
