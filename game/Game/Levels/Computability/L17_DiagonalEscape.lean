import Game.Metadata

World "Computability"
Level 17
Title "The Diagonal Escape"
-- source: ../game/Game/Worlds/W08Computability/L10DiagonalEscape.lean

Introduction "A final diagonal argument. Given any Boolean table of rows indexed by `ℕ`,
you can build a new row that differs from row `n` at position `n`, so it cannot equal any
listed row."

Statement (table : ℕ → ℕ → Bool) :
    ∃ diagonal : ℕ → Bool, ∀ n, diagonal ≠ table n := by
  Hint "Define `diagonal n` to be the negation of `table n n`."
  refine ⟨fun n => !(table n n), ?_⟩
  intro n h
  have := congrFun h n
  simp at this

Conclusion "Verified: diagonalization always escapes the table."
