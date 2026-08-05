import Game.Metadata
import Game.Support.Contracts

open scoped BigOperators

World "HoareTripleExercises"
Level 1
Title "Array Sum Accumulator"
-- source: RequestProject Lab04.suma_invariant, Lab04.suma_spec

Introduction "`suma` accumulates the array one entry at a time. Its loop
invariant — after `i` steps the accumulator equals the sum of the first
`i` entries — is exactly what `suma` computes at `n`. Prove it by
induction on the step count."

Statement (v : ℕ → Int) (n : ℕ) :
    Game.Contracts.suma v n = ∑ k ∈ Finset.range n, v k := by
  Hint "Unfold `suma` down to `sumaAux`, then induct on `n`."
  unfold Game.Contracts.suma
  induction n with
  | zero =>
    Hint (hidden := true) "`rw [sumaAux, Finset.range_zero, Finset.sum_empty]`."
    rw [Game.Contracts.sumaAux, Finset.range_zero, Finset.sum_empty]
  | succ i ih =>
    Hint (hidden := true) "`rw [sumaAux, ih, Finset.sum_range_succ]`."
    rw [Game.Contracts.sumaAux, ih, Finset.sum_range_succ]

Conclusion "Verified: the accumulator matches the running sum at every step."

NewDefinition Game.Contracts.suma Game.Contracts.sumaAux
NewTheorem Finset.range_zero Finset.sum_range_succ
