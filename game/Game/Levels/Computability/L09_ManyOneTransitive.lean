import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 9
Title "Reduction Relay"
-- source: ../game/Game/Worlds/W08Computability/L02ReductionTransitive.lean

Introduction "Compose two many-one reductions. The computable maps compose, and the
correctness equivalences chain through the intermediate problem."

Statement {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α → Prop} {q : β → Prop} {r : γ → Prop}
    (hpq : ManyOne p q) (hqr : ManyOne q r) : ManyOne p r := by
  Hint "Destructure both reductions, compose their functions with `Computable.comp`, then
  chain the two iff proofs."
  rcases hpq with ⟨f, hf, hpf⟩
  rcases hqr with ⟨g, hg, hqg⟩
  exact ⟨g ∘ f, hg.comp hf, fun x => (hpf x).trans (hqg (f x))⟩

Conclusion "Verified: many-one reducibility is transitive."

NewTheorem Computable.comp Iff.trans
