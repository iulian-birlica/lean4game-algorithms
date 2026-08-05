import Game.Metadata
import Game.Support.Design
import Game.Levels.Greedy.L07_DensityUpperBound

open Game.Design

World "Greedy"
Level 8
Title "Density Order Bound"
-- source: RequestProject Lab05.density_bound_of_sorted

Introduction "If the list is sorted by decreasing density, then every material
in the tail has density at most that of the head. That gives the exchange
argument its distinguished density `it.v / it.w`."

Statement density_bound_of_sorted_player (it : Item) (rest : List Item)
    (hpos : PosWeights (it :: rest)) (hsorted : SortedByDensity (it :: rest)) :
    ∀ b ∈ (it :: rest), b.v ≤ (it.v / it.w) * b.w := by
  Hint "Case on whether `b` is the head or in the tail."
  intro b hb
  cases' hb with hb hb
  · rw [div_mul_cancel₀ _ (ne_of_gt (hpos _ (by simp +decide only [List.mem_cons, true_or])))]
  · rw [div_mul_eq_mul_div, le_div_iff₀] <;>
      linarith [hpos it (by tauto), hpos b (by tauto),
        hsorted |> List.pairwise_cons.mp |>.1 b (by tauto)]

Conclusion "Sorted density means the head item is the density benchmark."

NewTactic cases'
NewDefinition Game.Design.SortedByDensity
NewTheorem div_mul_cancel₀ ne_of_gt div_mul_eq_mul_div le_div_iff₀ List.pairwise_cons
