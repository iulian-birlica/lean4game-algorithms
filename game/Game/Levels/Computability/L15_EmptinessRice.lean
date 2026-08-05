import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 15
Title "Emptiness Is Undecidable"
-- source: ../game/Game/Worlds/W08Computability/L08EmptinessRice.lean

Introduction "The property 'this program accepts nothing' is also extensional and
nontrivial. Rice's theorem therefore rules it out as decidable."

Statement : ¬ ComputablePred Game.Complexity.Empty := by
  rcases exists_empty_code with ⟨c, hc⟩
  simpa [Game.Complexity.Empty] using
    (rice_nontrivial
      (C := {d : Nat.Partrec.Code | Game.Complexity.Empty d})
      (invariant := by
        intro cf cg h
        simp [Game.Complexity.Empty, h])
      (yes := c)
      (no := Nat.Partrec.Code.const 0)
      (hyes := hc)
      (hno := const_zero_not_empty))

Conclusion "Verified: emptiness is undecidable."

NewTheorem Game.Complexity.const_zero_not_empty
