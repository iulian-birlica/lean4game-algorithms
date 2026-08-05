import Game.Metadata
import Game.Support.AdvancedStrings

open Game.AdvancedString

World "AdvancedStrings"
Level 5
Title "Valid Suffix Positions"

Introduction "A position is a valid suffix start exactly when it's within
range of the text, up to and including the empty suffix at the very end."

Statement {α : Type} (text : List α) (i : Nat) :
    i ∈ suffixIndices text ↔ i ≤ text.length := by
  Hint "Unfold `suffixIndices`, then rewrite membership in `List.range` and
  simplify the resulting successor bound."
  unfold suffixIndices
  rw [List.mem_range, Nat.lt_add_one_iff]

Conclusion "Membership in the index list is exactly the length bound."
