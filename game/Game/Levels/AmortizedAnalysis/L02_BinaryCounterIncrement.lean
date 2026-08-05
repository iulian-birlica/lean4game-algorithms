import Game.Metadata
import Game.Support.Clockwork

open Game.Clockwork

World "AmortizedAnalysis"
Level 2
Title "Binary Counter Increment"
-- source: RequestProject Lab16.increment_amortized

Introduction "The running example: a binary counter, bits
least-significant-first, with `increment` charging one unit per bit
written. Its potential `Phi` is the number of set bits. Prove the key
amortized bound: incrementing costs at most `2`, amortized — an
increment resets a run of `1`s (dropping the potential) and sets one `0`
(raising it by one), however long the carry chain is."

Statement (bs : List Bool) : incCost bs + Phi (increment bs) ≤ 2 + Phi bs := by
  Hint "Induct on `bs`; in the step case, split on the low bit."
  induction bs with
  | nil => simp only [incCost_nil, increment_nil, Phi_true, Phi_nil, zero_add, Nat.reduceAdd,
      add_zero, le_refl]
  | cons b bs ih =>
    Hint (hidden := true) "Case on `b`: a `0` bit is a one-step base case; a `1` bit recurses,
    combined with the induction hypothesis via `omega`."
    cases b with
    | false => simp only [incCost_false, increment_false, Phi_true, Phi_false]; omega
    | true => simp only [incCost_true, increment_true, Phi_false, Phi_true]; omega

Conclusion "Verified: incrementing the counter has amortized cost 2, no matter the carry chain."

NewDefinition Game.Clockwork.incrementT Game.Clockwork.increment
  Game.Clockwork.incCost Game.Clockwork.Phi
NewTheorem Game.Clockwork.incCost_nil Game.Clockwork.increment_nil
  Game.Clockwork.Phi_nil Game.Clockwork.Phi_true Game.Clockwork.Phi_false
  Game.Clockwork.incCost_false Game.Clockwork.increment_false
  Game.Clockwork.incCost_true Game.Clockwork.increment_true Nat.reduceAdd
