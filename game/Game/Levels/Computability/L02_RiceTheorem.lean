import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 2
Title "Rice's Theorem"
-- source: RequestProject Lab21.rice_nontrivial

Introduction "**Rice's theorem, index form** (given): a behaviour-invariant set of codes `C` —
one where membership only depends on `eval c`, never on `c`'s syntax — is computable iff it is
`∅` or everything. Package it: a behaviour-invariant `C` with both a member and a non-member is
undecidable. This one lemma is the engine behind every 'is this property of a program
undecidable?' corollary."

Statement {C : Set Nat.Partrec.Code}
    (H : ∀ cf cg : Nat.Partrec.Code, cf.eval = cg.eval → (cf ∈ C ↔ cg ∈ C))
    {c₀ c₁ : Nat.Partrec.Code} (h₀ : c₀ ∈ C) (h₁ : c₁ ∉ C) :
    ¬ ComputablePred (fun c => c ∈ C) := by
  Hint "Assume `C` were computable; by `rice_index` it is `∅` or everything, but `c₀ ∈ C` rules
  out `∅` and `c₁ ∉ C` rules out `Set.univ`."
  intro hcomp
  rcases (rice_index C H).mp hcomp with hempty | huniv
  · rw [hempty] at h₀; simp at h₀
  · rw [huniv] at h₁; exact h₁ (Set.mem_univ c₁)

Conclusion "Verified: any behaviour-invariant property with both a witness and a
counterexample is undecidable — Rice's theorem, ready to certify a whole family of
undecidability results."

NewDefinition Nat.Partrec.Code
NewTheorem Game.Complexity.rice_index Set.mem_univ
