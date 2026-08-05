import Game.Metadata
import Game.Support.Numeric

open Game.Numeric

World "NumericAlgorithms"
Level 9
Title "Sieve of Eratosthenes"
-- source: ../game/Game/Worlds/W12Numeric/L09SieveCorrect.lean

Introduction "The mathematical sieve output is just the primes up to the
given bound. Unfold `sieveCandidates` and simplify the `Finset.range`
membership condition."

Statement (bound n : Nat) :
    n ∈ sieveCandidates bound ↔ n ≤ bound ∧ Nat.Prime n := by
  Hint "After unfolding, `simp [Nat.lt_succ_iff]` turns membership in
  `Finset.range (bound + 1)` into the bound `n ≤ bound`."
  unfold sieveCandidates
  simp [Nat.lt_succ_iff]

Conclusion "The sieve keeps exactly the primes up to the chosen bound."

NewDefinition Game.Numeric.sieveCandidates
NewTactic unfold simp
NewTheorem Nat.lt_succ_iff
