import Game.Metadata
import Game.Support.Design

open Game.Design

World "DynamicProgramming"
Level 9
Title "Coin Recurrence"
-- source: RequestProject Lab06.minCoins_zero

Introduction "The coin-change DP recurrence `minCoins` needs no coins to
make change for `0`. Prove this base case by induction on the denomination
list."

Statement (coins : List ℕ) : minCoins coins 0 = 0 := by
  Hint "Induct on `coins`; the empty case unfolds directly, the `cons` case
  needs the `if`-branch of `cmin` to fire."
  induction' coins with c cs ih
  · simp only [minCoins]
  · Hint (hidden := true) "`simp [ih, nonpos_iff_eq_zero, zero_tsub]`, then unfold
    `cmin` and take the `if_pos` branch with `zero_le`."
    unfold minCoins
    simp +decide only [ih, nonpos_iff_eq_zero, zero_tsub]
    unfold cmin
    rw [if_pos (zero_le _)]

Conclusion "Verified: with nothing to pay, zero coins suffice."

NewTheorem nonpos_iff_eq_zero zero_tsub zero_le
