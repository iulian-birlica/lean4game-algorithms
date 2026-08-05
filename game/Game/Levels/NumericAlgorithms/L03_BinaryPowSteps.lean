import Game.Metadata
import Game.Support.Numeric

open Game.Numeric

World "NumericAlgorithms"
Level 3
Title "Binary Exponentiation Steps"
-- source: ../game/Game/Worlds/W12Numeric/L03BinaryPowSteps.lean

Introduction "On an exponent that is exactly a power of two, repeated
squaring processes one binary digit per round. Show that `powSteps (2 ^ bits)`
is exactly `bits + 1`."

Statement (bits : Nat) :
    powSteps (2 ^ bits) = bits + 1 := by
  Hint "First settle the base computation `powSteps 1 = 1`, then induct on
  `bits`. After unfolding, `grind` can finish the arithmetic."
  have base : powSteps 1 = 1 := by
    native_decide +revert
  induction' bits with bits ih
  · exact base
  · unfold powSteps
    grind

Conclusion "The power-of-two step count matches the number of processed bits."

NewDefinition Game.Numeric.powSteps
NewTactic induction' unfold native_decide grind
