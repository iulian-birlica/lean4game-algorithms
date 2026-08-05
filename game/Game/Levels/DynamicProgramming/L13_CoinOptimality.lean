import Game.Metadata
import Game.Support.Design
import Game.Levels.DynamicProgramming.L12_CoinLowerBound

open Game.Design

World "DynamicProgramming"
Level 13
Title "Coin Optimality"
-- source: RequestProject Lab06.minCoins_isLeast

Introduction "Now assemble the least-coins theorem from the smaller pieces:
one level gave a witness that attains `minCoins`, and another showed every
achievable count is at least `minCoins`."

Statement coin_change_is_least (coins : List ℕ) (amount : ℕ)
    (hpos : PosCoins coins) (hne : ∃ r, IsRep coins amount r) :
    IsLeast { n : ℕ∞ | ∃ r, IsRep coins amount r ∧ (r.length : ℕ∞) = n }
      (minCoins coins amount) := by
  Hint "`IsLeast` asks for membership and then a lower bound for every member."
  refine ⟨?_, ?_⟩
  · Hint (hidden := true) "Use the finite-value level, then the witness level."
    exact coin_value_witness coins amount (coin_value_finite coins amount hpos hne)
  · Hint (hidden := true) "The lower-bound level handles every member `n`."
    intro n hn
    exact coin_lower_bound coins amount hpos n hn

Conclusion "Coin change is split into clear achievability and lower-bound
steps."

NewTheorem coin_change_is_least
