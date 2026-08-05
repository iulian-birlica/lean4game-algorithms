import Game.Metadata
import Game.Support.Design

open Game.Design

World "Sequences"
Level 5
Title "Optimal BST Cost"
-- source: RequestProject Lab08.optCost_isLeast

Introduction "**Optimality of the interval DP.** `optCost w i len` is the
least achievable cost of any binary search tree shape storing the `len`
keys of `[i, i+len)`: the lower-bound and achievability theorems are
supplied — assemble them."

Statement (w : ℕ → ℕ) (i len : ℕ) :
    IsLeast {c | ∃ s : Shape, numKeys s = len ∧ tcost w s i = c} (optCost w i len) := by
  Hint "`IsLeast` needs membership (achievability) and a lower bound."
  Hint (hidden := true) "Use `exists_tcost_eq_optCost` for membership and
  `optCost_le_tcost` for the lower bound."
  constructor
  · obtain ⟨s, hs, hc⟩ := exists_tcost_eq_optCost w len i
    exact ⟨s, hs, hc⟩
  · rintro c ⟨s, hs, rfl⟩
    exact optCost_le_tcost w len i s hs

Conclusion "Verified: the interval DP is provably optimal."

NewDefinition Game.Design.Shape Game.Design.Shape.leaf Game.Design.Shape.node
  Game.Design.numKeys Game.Design.tcost Game.Design.optCost
NewTheorem Game.Design.exists_tcost_eq_optCost Game.Design.optCost_le_tcost
