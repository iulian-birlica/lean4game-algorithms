import Game.Metadata
import Game.Support.Numeric

open Game.Numeric

World "NumericAlgorithms"
Level 1
Title "Repeated-Squaring Invariant"
-- source: ../game/Game/Worlds/W12Numeric/L01BinaryPowInvariant.lean

Introduction "Fast exponentiation keeps an accumulator while repeatedly
squaring the base and halving the exponent. Prove the core invariant:
`binaryPowAux base exponent accumulator` always equals
`accumulator * base ^ exponent`."

Statement binaryPowAux_invariant (base exponent accumulator : Nat) :
    binaryPowAux base exponent accumulator = accumulator * base ^ exponent := by
  Hint "Use strong induction on `exponent`, then split it into the even and
  odd cases with `Nat.even_or_odd'`."
  induction' exponent using Nat.strong_induction_on with exponent ih
      generalizing base accumulator
  unfold binaryPowAux
  rcases Nat.even_or_odd' exponent with ⟨k, rfl | rfl⟩ <;>
      simp_all +decide [pow_succ, pow_mul]
  · cases k <;> simp_all +decide [mul_pow]
  · convert ih k (by omega) (base * base) (accumulator * base) using 1
    norm_num [Nat.add_div]
    ring

Conclusion "The accumulator invariant is established."

NewDefinition Game.Numeric.binaryPowAux
NewTactic induction' unfold rcases simp ring omega
NewTheorem Nat.even_or_odd' pow_succ pow_mul mul_pow Nat.add_div
