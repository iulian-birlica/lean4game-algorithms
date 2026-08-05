import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 14
Title "P Lies in coNP"
-- source: ../game/Game/Worlds/W07Complexity/L05PInsideCoNP.lean

Introduction "`coNP` consists of complements of `NP` problems. Since `P` is closed under
complement and `P ⊆ NP`, every polynomial-time problem also belongs to `coNP`."

Statement (problem : DecisionProblem) :
    inP problem → inCoNP problem := by
  Hint "First move from `problem ∈ P` to `compl problem ∈ P`, then apply `P_subset_NP`."
  intro hproblem
  exact P_subset_NP (inP_compl hproblem)

Conclusion "Verified: every problem in `P` also lies in `coNP`."

NewTheorem Game.Complexity.P_subset_NP Game.Complexity.inP_compl
