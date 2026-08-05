import Game.Metadata
import Game.Support.Complexity

open Game.Complexity
open Cslib.Algorithms.Lean

World "ComplexityClasses"
Level 2
Title "Reduction Calculus"
-- source: RequestProject Lab19.PolyReducible.refl, Lab19.PolyReducible.trans

Introduction "A **polynomial-time (many–one) reduction** `PolyReducible sizeA sizeB A B`
transforms every instance of `A` into an instance of `B`, preserving the answer, using only
polynomial time and blowing up the size only polynomially. Prove it is reflexive (every
problem reduces to itself, via the identity) and transitive (reductions chain)."

Statement {α β γ : Type*} {sizeA : α → ℕ} {sizeB : β → ℕ} {sizeC : γ → ℕ}
    {A : α → Prop} {B : β → Prop} {C : γ → Prop} :
    PolyReducible sizeA sizeA A A ∧
    (PolyReducible sizeA sizeB A B → PolyReducible sizeB sizeC B C → PolyReducible sizeA sizeC A C) := by
  Hint "Reflexivity is the identity map, computed for free (zero time, identity size). Transitivity
  composes the two witnessed maps/routines and combines their time/size bounds."
  refine ⟨?_, ?_⟩
  · use fun x => x, fun x => pure x
    refine' ⟨fun _ => 0, fun n => n, _, _, _, _, _⟩ <;>
      simp +decide only [IsPolyBounded.const, IsPolyBounded.id, TimeM.ret_pure, implies_true,
        TimeM.time_pure, le_refl, and_self]
  · Hint (hidden := true) "Destructure both reductions, combine their component bounds via
    `monomial_add_bound`/`monomial_comp_bound`, and note the composed map's routine costs the sum
    of the two routines' times."
    intro hAB hBC
    rcases hAB with ⟨f₁, red₁, t₁, s₁, ht₁, hs₁, hf₁, hAB₁, ht₁', hs₁'⟩
    rcases hBC with ⟨f₂, red₂, t₂, s₂, h_interm⟩
    obtain ⟨c₁, k₁, ht₁⟩ := ht₁
    obtain ⟨c₂, k₂, ht₂⟩ := h_interm.left
    obtain ⟨c₃, k₃, hs₁⟩ := hs₁
    obtain ⟨c₄, k₄, hs₂⟩ := h_interm.right.left
    use f₂ ∘ f₁
    refine' ⟨fun x => TimeM.mk (f₂ (f₁ x)) ((red₁ x |> TimeM.time) + (red₂ (f₁ x) |> TimeM.time)),
      fun n => (c₁ * (n + 1) ^ k₁) + (c₂ * (c₃ * (n + 1) ^ k₃ + 1) ^ k₂),
      fun n => c₄ * (c₃ * (n + 1) ^ k₃ + 1) ^ k₄, _, _, _, _, _⟩
    · exact ⟨c₁ + c₂ * (c₃ + 1) ^ k₂, k₁ ⊔ (k₃ * k₂), fun n => monomial_add_bound
        (by simp only [le_refl]) (by simpa only using monomial_comp_bound (by simp only [le_refl]))⟩
    · exact ⟨c₄ * (c₃ + 1) ^ k₄, k₃ * k₄, fun n => by simpa only [pow_mul, mul_assoc] using monomial_comp_bound (show c₃ * (n + 1) ^ k₃ ≤ c₃ * (n + 1) ^ k₃ from le_rfl)⟩
    · grobner
    · intro x; exact (hAB₁ x).trans (h_interm.2.2.2.1 (f₁ x))
    · refine' ⟨fun x => _, fun x => _⟩
      · refine' add_le_add (le_trans (ht₁' x) (ht₁ _))
          (le_trans (h_interm.2.2.2.2.1 _) (le_trans (ht₂ _) _))
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by linarith [hs₁' x, hs₁ (sizeA x)]) _)
      · exact le_trans (h_interm.2.2.2.2.2 _) (le_trans (hs₂ _)
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by linarith [hs₁ (sizeA x), hs₁' x]) _)))

Conclusion "Verified: polynomial reductions are reflexive and transitive — the calculus that
underlies every reduction argument in this world."

NewDefinition Game.Complexity.PolyReducible Cslib.Algorithms.Lean.TimeM.mk
  Cslib.Algorithms.Lean.TimeM.time
NewTactic grobner
NewTheorem Game.Complexity.IsPolyBounded.const Game.Complexity.IsPolyBounded.id pow_mul
  Nat.pow_le_pow_left Nat.mul_le_mul_left and_self
