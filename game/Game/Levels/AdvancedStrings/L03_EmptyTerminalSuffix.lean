import Game.Metadata
import Game.Support.AdvancedStrings

open Game.AdvancedString

World "AdvancedStrings"
Level 3
Title "Empty Terminal Suffix"

Introduction "The suffix starting right after the last symbol has nothing
left to contain: dropping the whole text's length leaves the empty list."

Statement {α : Type} (text : List α) : suffix text text.length = [] := by
  Hint "Unfold `suffix`: dropping a list's own length always leaves
  nothing."
  simp [suffix]

Conclusion "The suffix past the last symbol is always empty."
