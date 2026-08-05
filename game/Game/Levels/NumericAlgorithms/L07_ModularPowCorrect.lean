import Game.Metadata
import Game.Support.Numeric
import Game.Levels.NumericAlgorithms.L06_ModularPowInvariant

open Game.Numeric

World "NumericAlgorithms"
Level 7
Title "Modular Exponentiation Correctness"
-- source: ../game/Game/Worlds/W12Numeric/L07ModularPowCorrect.lean

Introduction "As before, correctness follows by starting the accumulator at
`1`. Use the modular invariant from the previous level."

Statement (modulus base exponent : Nat) :
    modularPow modulus base exponent = base ^ exponent % modulus := by
  Hint "Unfold `modularPow` via `simpa`, then specialize the previous
  invariant at accumulator `1`."
  simpa [modularPow] using modularPowAux_invariant modulus base exponent 1

Conclusion "Repeated squaring modulo `modulus` computes the desired residue."

NewDefinition Game.Numeric.modularPow
NewTactic simpa
NewTheorem modularPowAux_invariant
