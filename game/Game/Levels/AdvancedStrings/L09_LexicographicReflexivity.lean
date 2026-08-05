import Game.Metadata
import Game.Support.AdvancedStrings

open Game.AdvancedString

World "AdvancedStrings"
Level 9
Title "Lexicographic Reflexivity"

Introduction "`LexLE` compares two lists symbol by symbol, taking the
equal-heads branch whenever they agree. A list compares equal to itself at
every step, so it is always `LexLE`-related to itself."

Statement {α : Type} (lt : α → α → Prop) (text : List α) :
    LexLE lt text text := by
  Hint "Induct on `text`; matching heads take the equal-heads branch of
  `LexLE`, and the tails are handled by the induction hypothesis."
  induction text with
  | nil => simp [LexLE]
  | cons x xs ih => simp [LexLE, ih]

Conclusion "Every list is lexicographically no greater than itself."

NewDefinition Game.AdvancedString.LexLE
