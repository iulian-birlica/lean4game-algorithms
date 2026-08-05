import Game.Metadata
import Game.Support.AdvancedStrings

open Game.AdvancedString

World "AdvancedStrings"
Level 2
Title "Suffix Length Formula"

Introduction "The suffix starting at position `i` drops the first `i`
symbols, so its length is exactly what's left of the text."

Statement {α : Type} (text : List α) (i : Nat) :
    (suffix text i).length = text.length - i := by
  Hint "Unfold `suffix`; `List.length_drop` gives the formula directly."
  simp [suffix, List.length_drop]

Conclusion "A suffix's length is the text's length minus its start."
