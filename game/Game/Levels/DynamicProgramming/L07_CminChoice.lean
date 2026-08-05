import Game.Metadata
import Game.Support.Design

open Game.Design

World "DynamicProgramming"
Level 7
Title "Minimum Choice"
-- source: RequestProject Lab06.cmin_eq_left_or_right

Introduction "`cmin` does not invent a new value. It returns either the left
candidate or the right candidate. As a useful special case, `⊤` on the right
does not change the answer."

Statement (a b : ℕ∞) : (cmin a b = a ∨ cmin a b = b) ∧ cmin a ⊤ = a := by
  Hint "Prove the two facts separately; both only unfold `cmin` and split the
  `if`."
  refine ⟨?_, ?_⟩
  · unfold cmin
    by_cases h : a ≤ b
    · rw [if_pos h]
      exact Or.inl rfl
    · rw [if_neg h]
      exact Or.inr rfl
  · unfold cmin
    simp

Conclusion "For coin change, this lets us reason about the branch selected by
the recurrence without handling three facts at once."
