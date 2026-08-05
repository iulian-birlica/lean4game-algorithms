import Game.Metadata
import Game.Support.Design

open Game.Design

World "DynamicProgramming"
Level 8
Title "Carried Coin Value"

Introduction "`minCarry` is the coin-change analogue of `knapCarry`. It
returns `{ v : ℕ∞ // minCoins coins amount = v }`: the computed value, together
with a proof that it equals the reference recurrence.

The executable `coinImpl` is just the carried value."

Statement (coins : List ℕ) (amount : ℕ) :
    coinImpl coins amount = minCoins coins amount := by
  Hint "Use the proof component of `minCarry`; it points from `minCoins` to the
  carried value, so turn it around."
  Hint (hidden := true) "`exact (minCarry coins amount).2.symm`."
  exact (minCarry coins amount).2.symm

Conclusion "The coin-change implementation is correct by reading the proof
stored in its certificate."

NewDefinition Game.Design.minCoins Game.Design.minCarry Game.Design.coinImpl
