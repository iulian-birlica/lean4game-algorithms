import Game.Metadata
import Game.Support.AdvancedStrings

open Game.AdvancedString

World "AdvancedStrings"
Level 7
Title "Empty LCP"

Introduction "`lcp` is just the common-prefix measurement reused for suffix
comparisons. Against an empty word there is nothing to share a prefix with."

Statement {α : Type} [DecidableEq α] (text : List α) :
    lcp ([] : List α) text = 0 := by
  Hint "Unfold `lcp`: the common-prefix scan falls through to its base case
  whenever the first list is empty."
  rfl

Conclusion "An empty word has no longest common prefix with anything."

NewDefinition Game.AdvancedString.lcp
