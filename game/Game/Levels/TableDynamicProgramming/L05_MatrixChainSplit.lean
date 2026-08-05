import Game.Metadata
import Game.Support.TableDP

open Game.TableDP

World "TableDynamicProgramming"
Level 5
Title "Matrix-Chain Split"

Introduction "Matrix-chain DP improves an interval cell by comparing the current
best cost with one new split cost. The improved entry cannot exceed either the
old stored value or the new candidate."

/-- Improving a matrix-chain cell is bounded by the old value and the split candidate. -/
Statement (current left right rows middle cols : Nat) :
    improveMatrixChain current (matrixSplitCost left right rows middle cols) ≤ current ∧
    improveMatrixChain current (matrixSplitCost left right rows middle cols) ≤
      left + right + rows * middle * cols := by
  Hint "Unfold the matrix-chain definitions; the result is the two projections
  of `Nat.min`."
  unfold improveMatrixChain matrixSplitCost
  exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

Conclusion "A matrix-chain relaxation never increases the table cell."

NewTactic exact unfold
NewDefinition Game.TableDP.improveMatrixChain Game.TableDP.matrixSplitCost
NewTheorem Nat.min_le_left Nat.min_le_right
