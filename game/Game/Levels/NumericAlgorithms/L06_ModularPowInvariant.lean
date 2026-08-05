import Game.Metadata
import Game.Support.Numeric

open Game.Numeric

World "NumericAlgorithms"
Level 6
Title "Modular Repeated-Squaring Invariant"
-- source: ../game/Game/Worlds/W12Numeric/L06ModularPowInvariant.lean

Introduction "Modular repeated squaring carries the same accumulator idea as
ordinary fast exponentiation, except that every multiplication is reduced
modulo `modulus`. Prove the resulting invariant."

Statement modularPowAux_invariant (modulus base exponent accumulator : Nat) :
    modularPowAux modulus base exponent accumulator =
      (accumulator * base ^ exponent) % modulus := by
  Hint "Use strong induction on `exponent`, split into even and odd cases,
  and simplify with the modular arithmetic lemmas."
  induction' exponent using Nat.strong_induction_on with exponent ih
      generalizing base accumulator
  rcases Nat.even_or_odd' exponent with ⟨k, rfl | rfl⟩ <;>
      simp +decide [*, Nat.mul_mod, Nat.pow_succ', Nat.pow_mul]
  · unfold modularPowAux
    simp +decide [*, Nat.mul_mod, Nat.pow_mod]
    cases k <;> simp +decide [*, Nat.mul_mod, Nat.pow_mod]
    simp +decide
  · unfold modularPowAux
    simp +decide [*, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
    rw [ih]
    · norm_num [Nat.add_div]
      ring_nf
    · omega

Conclusion "The modular accumulator invariant is established."

NewDefinition Game.Numeric.modularPowAux
NewTactic induction' rcases unfold simp rw ring ring_nf omega
NewTheorem Nat.even_or_odd' Nat.mul_mod Nat.pow_succ' Nat.pow_mul Nat.pow_mod
  Nat.add_mod Nat.add_div
