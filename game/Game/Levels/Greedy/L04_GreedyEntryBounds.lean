import Game.Metadata
import Game.Support.Design

open Game.Design

World "Greedy"
Level 4
Title "Greedy Entry Bounds"
-- source: RequestProject Lab05.greedyAssign_entries

Introduction "The greedy assignment for continuous knapsack chooses one fraction
per material. Instead of proving all its safety facts from scratch, use the
proof-carrying certificate `greedyFeasibleCarry`: it stores the greedy list
together with a proof that the list is feasible."

Statement greedy_entry_bounds (items : List Item) (c : ℝ)
    (hpos : PosWeights items) (hc : 0 ≤ c) :
    ∀ xi ∈ greedyAssign items c, 0 ≤ xi ∧ xi ≤ 1 := by
  Hint "Let `cert := greedyFeasibleCarry items c hpos hc`. Its first proof says
  `cert.1` is the greedy assignment, and the feasibility proof inside `cert.2`
  contains the entrywise bounds."
  let cert := greedyFeasibleCarry items c hpos hc
  have hsame : cert.1 = greedyAssign items c := cert.2.1
  rw [← hsame]
  exact cert.2.2.2.1

Conclusion "The certificate exposes the entrywise `[0,1]` part of feasibility."

NewDefinition Game.Design.Item Game.Design.Item.w Game.Design.Item.v
  Game.Design.PosWeights Game.Design.greedyAssign Game.Design.Feasible
  Game.Design.greedyFeasibleCarry
