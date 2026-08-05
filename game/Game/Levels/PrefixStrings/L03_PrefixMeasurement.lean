import Game.Metadata
import Game.Support.PrefixStrings

open Game.String

World "PrefixStrings"
Level 3
Title "Prefix Measurement"

Introduction "If `pre` really is a prefix of `text`, the common-prefix scan
never has a reason to stop early: it walks the whole of `pre` matching
symbol for symbol. Unpack the reconstruction witness and induct on `pre`."

Statement {α : Type} [DecidableEq α] (pre text : List α) :
    IsPrefix pre text → commonPrefixLength pre text = pre.length := by
  Hint "Unpack the prefix witness with `rintro ⟨rest, rfl⟩`, then induct on
  `pre`."
  rintro ⟨rest, rfl⟩
  Hint (hidden := true) "Base case: both sides reduce to `0` by `rfl`. Step
  case: `simp [commonPrefixLength, ih]` unfolds one step and closes with the
  induction hypothesis."
  induction pre with
  | nil => rfl
  | cons x xs ih => simp [commonPrefixLength, ih]

Conclusion "A prefix is measured exactly by its own length."

NewDefinition Game.String.IsPrefix
