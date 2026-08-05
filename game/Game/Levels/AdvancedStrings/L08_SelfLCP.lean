import Game.Metadata
import Game.Support.AdvancedStrings

open Game.AdvancedString
open Game.String

World "AdvancedStrings"
Level 8
Title "Self LCP"

Introduction "A text shares its entire self with itself: the longest common
prefix of a text and a copy of itself is the whole text."

Statement {α : Type} [DecidableEq α] (text : List α) :
    lcp text text = text.length := by
  Hint "Unfold `lcp`, then induct on `text`; matching heads extend the
  measurement by one each step."
  unfold lcp
  induction text with
  | nil => rfl
  | cons x xs ih => simp [commonPrefixLength, ih]

Conclusion "A text's longest common prefix with itself is all of it."
