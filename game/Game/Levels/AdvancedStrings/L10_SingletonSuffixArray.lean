import Game.Metadata
import Game.Support.AdvancedStrings

open Game.AdvancedString

World "AdvancedStrings"
Level 10
Title "Singleton Suffix Array"

Introduction "A one-symbol text `[x]` has exactly two suffixes: the whole
text at position `0`, and the empty suffix at position `1`. The empty suffix
sorts first, so `[1, 0]` is the text's suffix array — check both halves of
the certificate."

Statement {α : Type} (lt : α → α → Prop) (x : α) :
    IsSuffixArray lt [x] [1, 0] := by
  Hint "Split the certificate: first that `[1, 0]` is a permutation of the
  valid suffix positions, then that it is pairwise lexicographically
  ordered."
  constructor
  · simp +decide [suffixIndices]
  · simp +decide [suffix, LexLE]

Conclusion "The empty suffix sorts before the whole text, as expected."

NewDefinition Game.AdvancedString.IsSuffixArray
