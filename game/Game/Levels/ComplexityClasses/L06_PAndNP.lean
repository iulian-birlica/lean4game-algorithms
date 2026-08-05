import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 6
Title "P and NP"
-- source: RequestProject Lab20.P_subset_NP, Lab20.inP_of_reduces, Lab20.inNP_of_reduces

Introduction "A **decision problem** bundles an input type, a size measure, and a yes/no
predicate. `P` is the class decided in polynomial time; `NP` is the class with polynomial-time
**verifiers** (a short certificate the verifier checks quickly). Prove `P ⊆ NP` (a P-solver is
an NP-verifier that ignores its certificate), then that reductions transport both kinds of
membership from the target back to the source — the class-level payoff of this world's
reduction calculus."

Statement {A B : DecisionProblem} :
    P ⊆ NP ∧
    (Reduces A B → inP B → inP A) ∧
    (Reduces A B → inNP B → inNP A) := by
  Hint "`P ⊆ NP`: take the certificate type to be `Unit` and run the solver, ignoring the
  certificate. The two reduction-transport facts are exactly Lab 19's composition principle
  (for `P`) and a direct reduction-composed-with-verifier construction (for `NP`)."
  refine ⟨?_, ?_, ?_⟩
  · intro L hL
    obtain ⟨solve, t, ht, hsolve⟩ := hL
    use Unit, fun _ => 0, fun x _ => solve x, fun _ => 0, t
    exact ⟨IsPolyBounded.const 0, ht, fun x => by aesop, fun x c _ => hsolve.2 x⟩
  · exact PolyTimeSolvable.of_reducible
  · Hint (hidden := true) "Destructure the reduction and the target's verifier; the new verifier
    runs the reduction then the old verifier, rejecting if the certificate is too large for the
    (possibly larger) reduced instance."
    intro h hB
    obtain ⟨f, red, t, s, ht, hs, hred₁, hred₂, hred₃, hred₄⟩ := h
    obtain ⟨Cert, encSize, verify, p, t, hp, ht, h₁, h₂⟩ := hB
    rcases hp with ⟨c₁, k₁, hp⟩
    rcases ht with ⟨c₂, k₂, ht⟩
    rcases hs with ⟨c₃, k₃, hs⟩
    refine' ⟨Cert, encSize, fun x c => _, fun n => c₁ * (c₃ * (n + 1) ^ k₃ + 1) ^ k₁,
      fun n => c₂ * (c₃ * (n + 1) ^ k₃ + 1) ^ k₂, _, _, _, _⟩
    exact let y := f x; if h : encSize c ≤ p (B.size y) then verify y c else ⟨Bool.false, 0⟩
    · refine' ⟨c₁ * (c₃ + 1) ^ k₁, k₃ * k₁, fun n => _⟩
      rw [mul_assoc, pow_mul]
      rw [← mul_pow]
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by nlinarith [pow_pos (Nat.succ_pos n) k₃]) _)
    · refine' ⟨c₂ * (c₃ + 1) ^ k₂, k₃ * k₂, fun n => _⟩
      rw [mul_assoc, pow_mul]
      rw [← mul_pow]
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (by nlinarith [pow_pos (Nat.succ_pos n) k₃]) _)
    · intro x; specialize hred₂ x; specialize h₁ (f x); simp_all +decide
      constructor <;> rintro ⟨c, hc₁, hc₂⟩
      · exact ⟨c, le_trans hc₁ (le_trans (hp _) (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (by linarith [hred₄ x, hs (A.size x)]) _))), by aesop⟩
      · grind
    · intro x c hc; by_cases h : encSize c ≤ p (B.size (f x)) <;> simp +decide [h]
      exact le_trans (h₂ _ _ h) (ht _ |> le_trans <| Nat.mul_le_mul_left _ <|
        Nat.pow_le_pow_left (by linarith [hred₄ x, hs (A.size x)]) _)

Conclusion "Verified: `P ⊆ NP`, and reductions transport membership in both classes. The reverse
containment `NP ⊆ P` — equivalently `P = NP` — is the central open problem of the field: it is
stated faithfully as a `Prop` (`PequalsNP`/`NP_subset_P_conjecture`) with no proof obligation
either way, never claimed as a theorem."

NewDefinition Game.Complexity.DecisionProblem Game.Complexity.inP Game.Complexity.inNP
  Game.Complexity.P Game.Complexity.NP Game.Complexity.Reduces Unit Bool
NewTactic specialize
NewTheorem Game.Complexity.PolyTimeSolvable.of_reducible mul_pow
