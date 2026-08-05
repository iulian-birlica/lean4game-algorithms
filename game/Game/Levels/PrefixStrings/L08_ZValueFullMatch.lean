import Game.Metadata
import Game.Support.PrefixStrings

open Game.String

World "PrefixStrings"
Level 8
Title "Z-Value Full Match"

Introduction "A Z value equal to the whole text's length means the suffix
starting there begins with a full copy of the text — the same prefix
characterization that proved KMP soundness, now instantiated with the whole
text playing the role of the pattern."

Statement {α : Type} [DecidableEq α] (text : List α) (position : Nat) :
    zValue text position = text.length ↔ IsPrefix text (text.drop position) := by
  Hint "Unfold `zValue`; this is the same prefix characterization used for
  KMP soundness, instantiated at `text` and `text.drop position`."
  unfold zValue
  Hint (hidden := true) "`exact commonPrefixLength_eq_length_iff_isPrefix text
  (text.drop position)`."
  exact commonPrefixLength_eq_length_iff_isPrefix text (text.drop position)

Conclusion "Reaching the whole text's length is exactly a full self-match."
