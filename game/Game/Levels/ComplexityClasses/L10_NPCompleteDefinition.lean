import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 10
Title "NP-Complete Definition"
-- source: ../game/Game/Worlds/W07Complexity/L01CompleteDefinition.lean

Introduction "`NPComplete problem` is just a bundled statement: the problem is both in `NP`
and `NP`-hard. Start the expansion by unfolding that definition exactly."

Statement (problem : DecisionProblem) :
    NPComplete problem ↔ inNP problem ∧ NPHard problem := by
  Hint "This is a definition-unfolding exercise."
  rfl

Conclusion "Verified: NP-completeness is exactly `inNP ∧ NPHard`."

NewDefinition Game.Complexity.NPHard Game.Complexity.NPComplete
