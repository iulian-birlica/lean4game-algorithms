import Game.Metadata
import Game.Support.Design

open Game.Design

World "DynamicProgramming"
Level 12
Title "Coin Lower Bound"
-- source: RequestProject Lab06.minCoins_isLeast

Introduction "The other half of optimality is lower-bound reasoning: every
representation uses at least as many coins as `minCoins`."

Statement coin_lower_bound (coins : List ℕ) (amount : ℕ)
    (hpos : PosCoins coins) (n : ℕ∞)
    (hn : ∃ r, IsRep coins amount r ∧ (r.length : ℕ∞) = n) :
    minCoins coins amount ≤ n := by
  Hint "Open the membership witness and apply the supplied lower-bound card."
  obtain ⟨r, hr, rfl⟩ := hn
  exact minCoins_le_of_rep coins amount hpos r hr

Conclusion "Every achievable coin count is above the DP count."

NewTheorem Game.Design.minCoins_le_of_rep coin_lower_bound
