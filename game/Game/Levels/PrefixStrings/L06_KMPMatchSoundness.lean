import Game.Metadata
import Game.Support.PrefixStrings

open Game.String

World "PrefixStrings"
Level 6
Title "KMP Match Soundness"

Introduction "A KMP match at `position` means the pattern's common-prefix scan
against the text from `position` reached the pattern's full length. Unfolding
the definitions turns this into exactly the prefix characterization already
established — for `xs := pattern` and `ys := text.drop position`."

Statement {α : Type} [DecidableEq α] (pattern text : List α) (position : Nat) :
    KMPMatch pattern text position ↔ IsPrefix pattern (text.drop position) := by
  Hint "Unfold `KMPMatch` and `kmpMatchLength`; the goal becomes the general
  prefix characterization instantiated at `pattern` and `text.drop position`."
  unfold KMPMatch kmpMatchLength
  Hint (hidden := true) "`exact commonPrefixLength_eq_length_iff_isPrefix
  pattern (text.drop position)`."
  exact commonPrefixLength_eq_length_iff_isPrefix pattern (text.drop position)

Conclusion "A KMP match at a position is exactly a true occurrence there."

NewDefinition Game.String.KMPMatch Game.String.kmpMatchLength
NewTheorem Game.String.commonPrefixLength_eq_length_iff_isPrefix
