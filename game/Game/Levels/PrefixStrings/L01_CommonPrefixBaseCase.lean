import Game.Metadata
import Game.Support.PrefixStrings

open Game.String

World "PrefixStrings"
Level 1
Title "Common Prefix Base Case"

Introduction "`commonPrefixLength` measures how far two lists agree from the
front. Its recursion only advances while both lists have a head to compare —
if the first list runs out, there is nothing left to match."

Statement {α : Type} [DecidableEq α] (word : List α) :
    commonPrefixLength ([] : List α) word = 0 := by
  Hint "The recursive definition falls through to its base case whenever
  the first list is empty, regardless of `word`."
  rfl

Conclusion "An empty word shares no symbols with anything."

NewDefinition Game.String.commonPrefixLength
