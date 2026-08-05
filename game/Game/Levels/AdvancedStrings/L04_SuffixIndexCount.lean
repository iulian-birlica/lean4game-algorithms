import Game.Metadata
import Game.Support.AdvancedStrings

open Game.AdvancedString

World "AdvancedStrings"
Level 4
Title "Suffix Index Count"

Introduction "A text of length `n` has one suffix starting at each position
`0` through `n`, including the empty suffix at the very end — that's `n + 1`
valid starting positions."

Statement {α : Type} (text : List α) :
    (suffixIndices text).length = text.length + 1 := by
  Hint "Unfold `suffixIndices`; `List.length_range` gives the count."
  simp [suffixIndices, List.length_range]

Conclusion "There are exactly `text.length + 1` suffix positions."

NewDefinition Game.AdvancedString.suffixIndices
NewTheorem List.length_range
