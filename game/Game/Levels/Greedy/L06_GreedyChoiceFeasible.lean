import Game.Metadata
import Game.Support.Design
import Game.Levels.Greedy.L05_GreedyWeightBound

open Game.Design

World "Greedy"
Level 6
Title "Greedy Choice Feasible"
-- source: RequestProject Lab05.greedyAssign_feasible

Introduction "Now recover the whole feasibility statement. The certificate's
second field is exactly a feasibility proof for its carried list."

Statement greedy_choice_feasible (items : List Item) (c : ℝ)
    (hpos : PosWeights items) (hc : 0 ≤ c) :
    Feasible items c (greedyAssign items c) := by
  Hint "Use `greedyFeasibleCarry`, rewrite the carried list to
  `greedyAssign items c`, then return the carried feasibility proof."
  let cert := greedyFeasibleCarry items c hpos hc
  have hsame : cert.1 = greedyAssign items c := cert.2.1
  rw [← hsame]
  exact cert.2.2

Conclusion "The whole feasibility proof comes from the carried certificate."
