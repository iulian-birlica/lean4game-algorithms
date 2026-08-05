import Game.Metadata
import Game.Support.Numeric
import Game.Levels.NumericAlgorithms.L01_BinaryPowInvariant

open Game.Numeric

World "NumericAlgorithms"
Level 2
Title "Fast Exponentiation Correctness"
-- source: ../game/Game/Worlds/W12Numeric/L02BinaryPowCorrect.lean

Introduction "The accumulator invariant from the previous level immediately
proves correctness: `binaryPow` is just `binaryPowAux` started at
accumulator `1`."

Statement (base exponent : Nat) :
    binaryPow base exponent = base ^ exponent := by
  Hint "Unfold `binaryPow` through `simpa`, then specialize the previous
  invariant at accumulator `1`."
  simpa [binaryPow] using binaryPowAux_invariant base exponent 1

Conclusion "Repeated squaring computes ordinary exponentiation."

NewDefinition Game.Numeric.binaryPow
NewTactic simpa
NewTheorem binaryPowAux_invariant
