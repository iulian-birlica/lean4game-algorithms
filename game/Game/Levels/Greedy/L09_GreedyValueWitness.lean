import Game.Metadata
import Game.Support.Design
import Game.Levels.Greedy.L08_DensityOrderBound

open Game.Design

World "Greedy"
Level 9
Title "Greedy Value Witness"
-- source: RequestProject Lab05.greedyAssign_feasible, Lab05.greedyAssign_value

Introduction "The greedy value is not just an upper bound on paper. Here a
second proof-carrying certificate packages a feasible choice together with the
proof that it attains the greedy value."

Statement greedy_value_witness (items : List Item) (c : ℝ)
    (hpos : PosWeights items) (hc : 0 ≤ c) :
    ∃ x, Feasible items c x ∧ totalValue items x = greedy items c := by
  Hint "Use `(greedyWitnessCarry items c hpos hc).1` as the witness. Its second
  component already contains both required proofs."
  let cert := greedyWitnessCarry items c hpos hc
  exact ⟨cert.1, cert.2⟩

Conclusion "The proof-carrying witness gives achievability with no extra
assembly."

NewDefinition Game.Design.greedy Game.Design.greedyWitnessCarry
