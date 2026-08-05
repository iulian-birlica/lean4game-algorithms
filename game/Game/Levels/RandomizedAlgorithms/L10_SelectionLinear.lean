import Game.Metadata
import Game.Support.Randomized

open Game.Randomized

World "RandomizedAlgorithms"
Level 10
Title "Randomized Selection Is Linear"
-- source: ../game/Game/Worlds/W10Randomized/L10SelectionLinear.lean

Introduction "The geometric expected-work recurrence for randomized selection
stays below `2n`, so the model has linear expected growth."

Statement (n : Nat) :
    selectionExpectedWork n ≤ 2 * n := by
  Hint "Induct on `n`. Each new stage adds `n + 1`, while only half of the
  previous expected work remains."
  induction' n with n ih
  · norm_num [selectionExpectedWork]
  · norm_num [selectionExpectedWork] at ih ⊢
    linarith

Conclusion "The recurrence now has a linear upper bound."

NewDefinition Game.Randomized.selectionExpectedWork
NewTactic induction' norm_num linarith
