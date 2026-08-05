import Game.Metadata
import Game.Support.Randomized

open Game.Randomized

World "RandomizedAlgorithms"
Level 3
Title "Expectation of a Constant"
-- source: ../game/Game/Worlds/W10Randomized/L03ConstantExpectation.lean

Introduction "A constant-valued random variable should have that same constant
as its expectation on any nonempty finite experiment."

Statement (σ : Type) (seeds : List σ) (value : ℚ) :
    seeds ≠ [] → expectation seeds (fun _ => value) = value := by
  Hint "Unfold `expectation`, rewrite the mapped list as a replicate, and let
  `simp` evaluate the sum."
  intro h_nonempty
  unfold expectation
  simp [h_nonempty, List.sum_replicate]

Conclusion "Constant random variables keep their constant expectation."

NewDefinition Game.Randomized.expectation
NewTheorem List.sum_replicate
