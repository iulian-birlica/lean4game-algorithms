import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L06_QuadraticVsCubic

open Game.Clockwork

World "Asymptotics"
Level 8
Title "Big-O Calculus"
-- source: RequestProject Lab11.IsBigO.refl, Lab11.IsBigO.trans

Introduction "From correctness we turn to *efficiency*: Landau notation for
comparing how functions grow. `f =O g` means `|f|` is eventually bounded by
a constant multiple of `|g|`. Show `=O` is a preorder: reflexive and
transitive."

/-- Big-O is reflexive and transitive. -/
Statement bigO_calculus (f g h : ℕ → ℝ) : f =O f ∧ (f =O g → g =O h → f =O h) := by
  Hint "Prove reflexivity first (witness `C = 1`, `N = 0`), then transitivity."
  constructor
  · use 1, by norm_num, 0
    norm_num
  · intro hfg hgh
    Hint (hidden := true) "Destructure both witnesses. The new constant is `C₁ * C₂`, and the new threshold is `max N₁ N₂`."
    obtain ⟨C₁, hC₁, N₁, hN₁⟩ := hfg
    obtain ⟨C₂, hC₂, N₂, hN₂⟩ := hgh
    exact ⟨C₁ * C₂, mul_pos hC₁ hC₂, N₁ ⊔ N₂, fun n hn => by
      Hint (hidden := true) "First use the `f =O g` bound, then the `g =O h` bound, and finally simplify with `simpa`."
      simpa only [mul_assoc, abs_mul] using
        le_trans (hN₁ n (le_trans (le_max_left _ _) hn))
          (mul_le_mul_of_nonneg_left (hN₂ n (le_trans (le_max_right _ _) hn)) hC₁.le)⟩

Conclusion "Verified: `=O` is reflexive and transitive."

NewTactic use simpa
NewTheorem mul_pos mul_assoc bigO_calculus
