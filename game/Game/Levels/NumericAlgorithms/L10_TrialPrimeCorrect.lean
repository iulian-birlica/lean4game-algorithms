import Game.Metadata
import Game.Support.Numeric

open Game.Numeric

World "NumericAlgorithms"
Level 10
Title "Trial-Division Primality"
-- source: ../game/Game/Worlds/W12Numeric/L10TrialPrimeCorrect.lean

Introduction "The executable test `trialPrime` accepts exactly the natural
numbers with no nontrivial divisors. Split on whether `n ≥ 2`, then compare
the definition with `Nat.prime_def_lt'`."

Statement (n : Nat) :
    trialPrime n = true ↔ Nat.Prime n := by
  Hint "Split on `2 ≤ n`. In the main case, unfold `trialPrime` and
  `trialDivisors`; in the small cases, `interval_cases` finishes."
  by_cases h : 2 ≤ n <;> simp_all +decide [Nat.prime_def_lt']
  · simp [trialPrime, trialDivisors]
    grind
  · interval_cases n <;> trivial

Conclusion "Trial division recognizes exactly the primes."

NewDefinition Game.Numeric.trialDivisors Game.Numeric.trialPrime
NewTactic by_cases simp interval_cases grind trivial
NewTheorem Nat.prime_def_lt'
