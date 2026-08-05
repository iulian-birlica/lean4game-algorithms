import Game.Metadata
import Game.Support.Design
import Game.Levels.Greedy.L11_GreedyOptimality

open Game.Design

World "Greedy"
Level 12
Title "Certified Greedy Knapsack"
-- source: RequestProject Lab05.greedyImpl_correct

Introduction "`greedyCarry` computes the greedy value together with a proof
that the value is correct. The final implementation theorem just reads that
proof back out."

Statement (items : List Item) (c : ℝ) : greedyImpl items c = greedy items c := by
  Hint "The equality is stored as the proof component of `greedyCarry`."
  Hint (hidden := true) "`exact (greedyCarry items c).2.symm`."
  exact (greedyCarry items c).2.symm

Conclusion "The executable implementation matches the reference greedy specification."

NewDefinition Game.Design.greedyImpl Game.Design.greedyCarry
