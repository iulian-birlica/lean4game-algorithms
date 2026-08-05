import Game.Metadata
import Game.Support.Design

open Game.Design

World "DynamicProgramming"
Level 11
Title "Coin Value Witness"
-- source: RequestProject Lab06.minCoins_isLeast

Introduction "A finite DP value is not just a number. The achievability card
`minCoins_achievable` gives an actual representation whose length is that
number."

Statement coin_value_witness (coins : List ℕ) (amount : ℕ)
    (hfinite : minCoins coins amount ≠ ⊤) :
    ∃ r, IsRep coins amount r ∧ (r.length : ℕ∞) = minCoins coins amount := by
  Hint "First extract the natural number hidden inside the finite `ℕ∞` value."
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
  Hint (hidden := true) "Use `minCoins_achievable` with `hn.symm`, then rewrite
  the representation length."
  obtain ⟨r, hr, hrlen⟩ := minCoins_achievable coins amount n hn.symm
  exact ⟨r, hr, by rw [hrlen]; exact hn⟩

Conclusion "The DP value is attained by some concrete coin representation."

NewTactic obtain
NewTheorem WithTop.ne_top_iff_exists Game.Design.minCoins_achievable coin_value_witness
