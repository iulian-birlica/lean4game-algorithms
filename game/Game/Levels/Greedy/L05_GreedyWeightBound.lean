import Game.Metadata
import Game.Support.Design
import Game.Levels.Greedy.L04_GreedyEntryBounds

open Game.Design

World "Greedy"
Level 5
Title "Greedy Weight Bound"
-- source: RequestProject Lab05.greedyAssign_used

Introduction "The next safety fact is global rather than entrywise: the greedy
choice never uses more weight than the knapsack capacity allows. The same
certificate already carries that fact."

Statement greedy_weight_bound (items : List Item) (c : ℝ)
    (hpos : PosWeights items) (hc : 0 ≤ c) :
    usedWeight items (greedyAssign items c) ≤ c := by
  Hint "Build the same certificate as before, rewrite `greedyAssign items c`
  to its carried list, and project the capacity part of `Feasible`."
  let cert := greedyFeasibleCarry items c hpos hc
  have hsame : cert.1 = greedyAssign items c := cert.2.1
  rw [← hsame]
  exact cert.2.2.2.2

Conclusion "The certificate also exposes the capacity part of feasibility."

NewDefinition Game.Design.usedWeight
