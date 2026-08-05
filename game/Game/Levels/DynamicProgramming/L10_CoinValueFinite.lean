import Game.Metadata
import Game.Support.Design

open Game.Design

World "DynamicProgramming"
Level 10
Title "Coin Value Is Finite"
-- source: RequestProject Lab06.minCoins_isLeast

Introduction "If some representation exists, the DP answer cannot be `⊤`.
The supplied theorem `minCoins_top_iff_no_rep` says that `⊤` means there is no
representation at all."

Statement coin_value_finite (coins : List ℕ) (amount : ℕ)
    (hpos : PosCoins coins) (hne : ∃ r, IsRep coins amount r) :
    minCoins coins amount ≠ ⊤ := by
  Hint "Turn a hypothetical `minCoins coins amount = ⊤` into a contradiction
  with the existing representation."
  intro htop
  exact (minCoins_top_iff_no_rep coins amount hpos).mp htop hne

Conclusion "Whenever change can be made, the recurrence returns a finite
number of coins."

NewDefinition Game.Design.PosCoins Game.Design.IsRep
NewTheorem Game.Design.minCoins_top_iff_no_rep coin_value_finite
