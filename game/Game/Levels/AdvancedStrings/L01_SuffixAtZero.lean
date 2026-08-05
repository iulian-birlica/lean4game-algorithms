import Game.Metadata
import Game.Support.AdvancedStrings

open Game.AdvancedString

World "AdvancedStrings"
Level 1
Title "Suffix At Zero"

Introduction "The suffix starting at position `0` is the whole text: dropping
nothing changes nothing."

Statement {α : Type} (text : List α) : suffix text 0 = text := by
  Hint "Unfold `suffix`: dropping zero elements returns the list unchanged."
  simp [suffix]

Conclusion "Position zero's suffix is the text itself."

NewDefinition Game.AdvancedString.suffix
