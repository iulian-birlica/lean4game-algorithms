import Game.Metadata
import Game.Support.PrefixStrings

open Game.String

World "PrefixStrings"
Level 4
Title "Border Length Bound"

Introduction "A border of `text` is both a prefix and a suffix of it. Being a
prefix alone already forces it to be no longer than `text` itself."

Statement {α : Type} (border text : List α) :
    IsBorder border text → border.length ≤ text.length := by
  Hint "A border is in particular a prefix; unpack its reconstruction
  witness and discard the suffix half."
  rintro ⟨⟨rest, htext⟩, _⟩
  Hint (hidden := true) "Rewrite `text` via the witness, expand the append's
  length, and close with `omega`."
  simp only [htext, List.length_append]
  omega

Conclusion "No border can outgrow the text it borders."

NewDefinition Game.String.IsBorder Game.String.IsSuffix
NewTheorem List.length_append
