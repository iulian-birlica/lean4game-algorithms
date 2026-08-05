import Game.Metadata
import Game.Support.Design
import Game.Levels.DynamicProgramming.L13_CoinOptimality

open Game.Design

World "DynamicProgramming"
Level 14
Title "Certified Coin Change"
-- source: RequestProject Lab06.coinImpl_correct, Lab06.coinImpl_isLeast

Introduction "You already extracted the proof that `coinImpl` equals
`minCoins`. Combine that carried equality with the least-coins theorem
assembled in the previous level."

Statement (coins : List ℕ) (amount : ℕ) (hpos : PosCoins coins)
    (hne : ∃ r, IsRep coins amount r) :
    coinImpl coins amount = minCoins coins amount ∧
      IsLeast { n : ℕ∞ | ∃ r, IsRep coins amount r ∧ (r.length : ℕ∞) = n }
        (coinImpl coins amount) := by
  Hint "Read off the bundled proof first, then rewrite the least-coins
  theorem through it."
  have h : coinImpl coins amount = minCoins coins amount := (minCarry coins amount).2.symm
  refine ⟨h, ?_⟩
  Hint (hidden := true) "`rw [h]; exact coin_change_is_least coins amount hpos hne`."
  rw [h]
  exact coin_change_is_least coins amount hpos hne

Conclusion "Certified: the proof-carrying coin changer is least-coins, for free."
