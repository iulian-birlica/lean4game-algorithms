import Game.Metadata
import Game.Support.Complexity

open Game.Complexity
open Nat.Partrec

World "Computability"
Level 13
Title "The Halting Asymmetry"
-- source: ../game/Game/Worlds/W08Computability/L06HaltingAsymmetry.lean

Introduction "Halting on a fixed input is semi-decidable: you can simulate and accept once
the program stops. Non-halting is not co-semi-decidable, so the two sides are genuinely
asymmetric."

Statement (n : ℕ) :
    SemiDecidable (fun c : Nat.Partrec.Code => (c.eval n).Dom) ∧
    ¬ CoSemiDecidable (fun c : Nat.Partrec.Code => (c.eval n).Dom) := by
  Hint "Use `halting_re` for semi-decidability and `halting_compl_not_re` for the
  complement."
  constructor
  · exact halting_re n
  · simpa [CoSemiDecidable] using halting_compl_not_re n

Conclusion "Verified: halting is r.e., but non-halting is not."

NewTheorem Game.Complexity.halting_re Game.Complexity.halting_compl_not_re
