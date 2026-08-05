import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 1
Title "Polynomial Time Reductions"
-- source: RequestProject Lab19.IsPolyBounded.add, Lab19.IsPolyBounded.comp

Introduction "This world is about **relating problems by their difficulty**. The substrate is
`IsPolyBounded t`: `t` is dominated by a single monomial `c·(n+1)^k`. Prove the one closure
property the whole theory rests on: polynomially bounded functions are closed under
(pointwise) addition and under composition."

Statement {t u : ℕ → ℕ} (ht : IsPolyBounded t) (hu : IsPolyBounded u) :
    IsPolyBounded (fun n => t n + u n) ∧ IsPolyBounded (fun n => t (u n)) := by
  Hint "Both halves reduce to the supplied monomial-arithmetic lemmas
  `monomial_add_bound`/`monomial_comp_bound`, applied to the witnesses `IsPolyBounded`
  provides via `.choose`/`.choose_spec` (or `obtain`)."
  refine ⟨?_, ?_⟩
  · exact ⟨ht.choose + hu.choose, max ht.choose_spec.choose hu.choose_spec.choose,
      fun n => monomial_add_bound (ht.choose_spec.choose_spec n) (hu.choose_spec.choose_spec n)⟩
  · Hint (hidden := true) "Destructure both witnesses via `obtain`, then feed
    `monomial_comp_bound` the inner bound."
    obtain ⟨c, k, hc⟩ := ht
    obtain ⟨cs, ks, hcs⟩ := hu
    exact ⟨c * (cs + 1) ^ k, ks * k,
      fun n => by simpa only [mul_assoc] using le_trans (hc _) (monomial_comp_bound (hcs _))⟩

Conclusion "Verified: polynomially bounded functions are closed under addition and composition."

NewDefinition Game.Complexity.IsPolyBounded
NewTheorem Game.Complexity.monomial_add_bound Game.Complexity.monomial_comp_bound
