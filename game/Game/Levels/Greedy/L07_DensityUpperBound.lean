import Game.Metadata
import Game.Support.Design
import Game.Levels.Greedy.L06_GreedyChoiceFeasible

open Game.Design

World "Greedy"
Level 7
Title "Density Upper Bound"
-- source: RequestProject Lab05.value_le_density_weight

Introduction "Once every material has density at most `ρ`, no non-negative
choice can get value more than `ρ` times the weight it uses."

Statement value_le_density_weight_player (items : List Item) (x : List ℝ) (ρ : ℝ)
    (hden : ∀ it ∈ items, it.v ≤ ρ * it.w) (hx : ∀ xi ∈ x, 0 ≤ xi) :
    totalValue items x ≤ ρ * usedWeight items x := by
  Hint "Induct on `items`, case on `x`, bound the head term, and reuse the
  induction hypothesis on the tail."
  induction items generalizing x with
  | nil => simp only [totalValue, usedWeight, mul_zero, le_refl]
  | cons it its ih =>
    cases x with
    | nil => simp only [totalValue, usedWeight, mul_zero, le_refl]
    | cons x0 xs =>
      have hx0 : 0 ≤ x0 := hx x0 (by simp only [List.mem_cons, true_or])
      have hitv : it.v ≤ ρ * it.w := hden it (by simp only [List.mem_cons, true_or])
      have hih : totalValue its xs ≤ ρ * usedWeight its xs :=
        ih xs
          (fun it' h => hden it' (by simp only [List.mem_cons, h, or_true]))
          (fun xi h => hx xi (by simp only [List.mem_cons, h, or_true]))
      have hmul : x0 * it.v ≤ x0 * (ρ * it.w) := mul_le_mul_of_nonneg_left hitv hx0
      simp only [totalValue, usedWeight]
      nlinarith [hmul, hih]

Conclusion "A density cap gives an immediate value cap."

NewTactic nlinarith
NewDefinition Game.Design.totalValue
NewTheorem mul_le_mul_of_nonneg_left or_true MulZeroClass.mul_zero true_or
