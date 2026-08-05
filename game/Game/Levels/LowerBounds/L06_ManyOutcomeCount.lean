import Game.Metadata
import Game.Support.LowerBounds

open Game.LowerBounds

World "LowerBounds"
Level 6
Title "Count Multiway Transcripts"
-- source: ../game/Game/Worlds/W14LowerBounds/L06ManyOutcomeCount.lean

Introduction "If each query has `outcomes` many answers, then a depth-`queries`
transcript is just a function `Fin queries → Fin outcomes`."

Statement (outcomes queries : Nat) :
    Fintype.card (Transcript outcomes queries) = outcomes ^ queries := by
  Hint "Count finite functions into `Fin outcomes`."
  simp [Fintype.card_pi]

Conclusion "Multiway decision trees have `outcomes ^ queries` transcripts."

NewDefinition Game.LowerBounds.Transcript
NewTheorem Fintype.card_pi
