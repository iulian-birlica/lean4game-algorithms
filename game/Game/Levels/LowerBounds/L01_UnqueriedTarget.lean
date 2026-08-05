import Game.Metadata
import Game.Support.LowerBounds

open Game.LowerBounds

World "LowerBounds"
Level 1
Title "Adversary: One Target Remains"
-- source: ../game/Game/Worlds/W14LowerBounds/L01UnqueriedTarget.lean

Introduction "If you have queried fewer positions than there are possible
targets, an adversary can still hide the target somewhere you did not ask
about."

Statement (α : Type) [Fintype α] [DecidableEq α] (queried : Finset α) :
    queried.card < Fintype.card α → ∃ target, AdversarySurvives queried target := by
  Hint "Assume every target was queried and compare `queried` with
  `Finset.univ`."
  classical
  intro h
  by_contra hnone
  push_neg at hnone
  exact (not_le_of_gt h) <|
    Finset.card_le_card <|
      show Finset.univ ⊆ queried from fun x _ => by
        simpa [AdversarySurvives] using hnone x

Conclusion "A strict counting gap leaves an unseen target."

NewDefinition Game.LowerBounds.AdversarySurvives
NewTheorem Finset.card_le_card not_le_of_gt
