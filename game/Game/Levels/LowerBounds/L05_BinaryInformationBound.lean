import Game.Metadata
import Game.Support.LowerBounds

open Game.LowerBounds

World "LowerBounds"
Level 5
Title "Binary Information Bound"
-- source: ../game/Game/Worlds/W14LowerBounds/L05BinaryInformationBound.lean

Introduction "If binary transcripts separate all hidden instances, the number
of instances cannot exceed the number of possible transcripts."

Statement (α : Type) [Fintype α] (queries : Nat)
    (encode : α → BinaryTranscript queries) :
    Separates encode → Fintype.card α ≤ 2 ^ queries := by
  Hint "Injectivity gives a cardinality bound into the transcript space."
  intro h
  simpa using Fintype.card_le_of_injective encode h

Conclusion "Distinct hidden instances require distinct binary transcripts."

NewDefinition Game.LowerBounds.Separates
NewTheorem Fintype.card_le_of_injective
