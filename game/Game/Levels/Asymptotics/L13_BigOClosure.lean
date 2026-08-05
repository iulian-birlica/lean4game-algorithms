import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L12_ChainingGrowthBounds

open Game.Clockwork

World "Asymptotics"
Level 13
Title "Big-O Closure"
-- source: RequestProject Lab11.isBigO_const_mul, Lab11.IsBigO.add

Introduction "The growth-rate algebra: scaling by a constant doesn't change
a function's class, and a sum of two `O(g)` functions is still `O(g)`."

Statement (c : ℝ) (f f₁ f₂ g : ℕ → ℝ) (h₁ : f₁ =O g) (h₂ : f₂ =O g) :
    (fun n => c * f n) =O f ∧ (fun n => f₁ n + f₂ n) =O g := by
  Hint "Prove the two closure facts separately."
  constructor
  · Hint (hidden := true) "Witness `C = |c| + 1`, `N = 0`."
    use |c| + 1
    · positivity
    use 0
    intro n hn
    Hint (hidden := true) "Rewrite `|c * f n|` as `|c| * |f n|`, then bound `|c|` by `|c| + 1`."
    simpa only [abs_mul] using
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (abs_nonneg _)
  · Hint (hidden := true) "Destructure both witnesses; the new constant is `C₁ + C₂`."
    obtain ⟨C₁, hC₁, N₁, hN₁⟩ := h₁
    obtain ⟨C₂, hC₂, N₂, hN₂⟩ := h₂
    Hint (hidden := true) "Use `abs_le` to split the goal into upper and lower bounds, then let `nlinarith` combine the two hypotheses."
    exact ⟨C₁ + C₂, by positivity, N₁ ⊔ N₂, fun n hn => by
      rw [abs_le]; constructor <;> cases abs_cases (g n) <;>
        nlinarith [abs_le.mp (hN₁ n (le_trans (le_max_left _ _) hn)),
          abs_le.mp (hN₂ n (le_trans (le_max_right _ _) hn))]⟩

Conclusion "Verified: growth classes are closed under scaling and addition."

NewTactic positivity
NewTheorem abs_mul mul_le_mul_of_nonneg_right le_add_of_nonneg_right abs_nonneg abs_le
  abs_cases zero_le_one
