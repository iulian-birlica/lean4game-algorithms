import Game.Metadata
import Game.Support.TableDP

open Game.TableDP

World "TableDynamicProgramming"
Level 1
Title "Edit-Distance Recurrence"

Introduction "An edit-distance table cell chooses the cheapest among deletion,
insertion, and substitution. Prove that the stored update is no larger than
each candidate it was allowed to choose."

/-- The edit-distance update is bounded by deletion, insertion, and substitution candidates. -/
Statement (deletion insertion substitution : Nat) :
    editUpdate deletion insertion substitution ≤ deletion + 1 ∧
    editUpdate deletion insertion substitution ≤ insertion + 1 ∧
    editUpdate deletion insertion substitution ≤ substitution := by
  Hint "Unfold `editUpdate`; the goal is just three facts about nested
  `Nat.min` expressions."
  unfold editUpdate
  constructor
  · exact Nat.min_le_left _ _
  · constructor
    · exact le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
    · exact le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)

Conclusion "The recurrence update is bounded by every edit candidate."

NewTactic constructor exact unfold
NewDefinition Game.TableDP.editUpdate
NewTheorem Nat.min_le_left Nat.min_le_right le_trans
