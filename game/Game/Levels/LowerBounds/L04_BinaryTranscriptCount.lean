import Game.Metadata
import Game.Support.LowerBounds

open Game.LowerBounds

World "LowerBounds"
Level 4
Title "Count Binary Transcripts"
-- source: ../game/Game/Worlds/W14LowerBounds/L04BinaryTranscriptCount.lean

Introduction "A binary transcript of depth `queries` is just a function from
`Fin queries` into `Bool`, so there are exactly `2 ^ queries` of them."

Statement (queries : Nat) :
    Fintype.card (BinaryTranscript queries) = 2 ^ queries := by
  Hint "This is a direct finite-function count."
  simp

Conclusion "Binary decision trees have exactly `2 ^ queries` transcripts."

NewDefinition Game.LowerBounds.BinaryTranscript
