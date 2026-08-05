import Game.Metadata
import Game.Support.AdvancedStrings

open Game.AdvancedString

World "AdvancedStrings"
Level 6
Title "Suffix List Count"

Introduction "Building the list of all suffixes just maps the suffix
positions to suffixes — mapping never changes how many entries there are."

Statement {α : Type} (text : List α) :
    (suffixes text).length = text.length + 1 := by
  Hint "Unfold `suffixes`; mapping preserves length, and the index count is
  already known."
  simp [suffixes, suffixIndices, List.length_map, List.length_range]

Conclusion "There is exactly one suffix per valid starting position."

NewDefinition Game.AdvancedString.suffixes
NewTheorem List.length_map
