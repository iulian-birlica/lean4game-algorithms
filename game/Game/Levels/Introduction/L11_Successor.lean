import Game.Metadata

World "Intro"
Level 11
Title "Successor"

Introduction "Natural numbers are built from `0` and `Nat.succ`.
`Nat.succ n` means 'the next number after `n`' — the same number usually
written `n + 1`."

Statement : ∀ n : ℕ, Nat.succ n = n + 1 := by
  intro n
  Hint "Both sides compute to the same natural number."
  rfl

Conclusion "`Nat.succ` is Lean's basic way to talk about the next natural number."

NewDefinition Nat.succ
OnlyTactic intro rfl
