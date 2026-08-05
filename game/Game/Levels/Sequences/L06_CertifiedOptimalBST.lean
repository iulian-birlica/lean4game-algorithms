import Game.Metadata
import Game.Support.Design

open Game.Design

World "Sequences"
Level 6
Title "Certified Optimal BST"
-- source: RequestProject Lab08.optImpl_correct, Lab08.optImpl_isLeast

Introduction "`optCarry` recomputes the interval DP while carrying a proof
that it equals the reference `optCost`. Correctness is a one-liner, and
optimality transfers for free to the proof-carrying implementation."

Statement (w : ℕ → ℕ) (i len : ℕ) :
    optImpl w i len = optCost w i len ∧
      IsLeast {c | ∃ s : Shape, numKeys s = len ∧ tcost w s i = c} (optImpl w i len) := by
  Hint "Read off the bundled proof first, then rewrite the optimality theorem
  through it."
  have h : optImpl w i len = optCost w i len := (optCarry w i len).2.symm
  refine ⟨h, ?_⟩
  Hint (hidden := true) "`rw [h]; exact optCost_isLeast w i len`."
  rw [h]
  exact optCost_isLeast w i len

Conclusion "Certified: the proof-carrying interval DP is optimal, for free."

NewDefinition Game.Design.optImpl Game.Design.optCarry
NewTheorem Game.Design.optCost_isLeast
