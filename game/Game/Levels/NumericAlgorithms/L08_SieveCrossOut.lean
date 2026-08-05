import Game.Metadata
import Game.Support.Numeric

open Game.Numeric

World "NumericAlgorithms"
Level 8
Title "Cross Out Multiples"
-- source: ../game/Game/Worlds/W12Numeric/L08SieveCrossOut.lean

Introduction "One sieve pass keeps exactly the candidates not divisible by the
chosen pivot `p`. Unfold the filtered `Finset` definition and characterize
membership."

Statement (p n : Nat) (candidates : Finset Nat) :
    n ∈ crossOut p candidates ↔ n ∈ candidates ∧ ¬p ∣ n := by
  Hint "Unfold `crossOut` and simplify membership in `Finset.filter`."
  unfold crossOut
  simp

Conclusion "A crossing-out pass removes exactly the multiples of `p`."

NewDefinition Game.Numeric.crossOut
NewTactic unfold simp
