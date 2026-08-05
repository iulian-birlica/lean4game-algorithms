import Game.Metadata

World "ProofEngineering"
Level 6
Title "Read the Theorem Type"
-- source: ../game/Game/Worlds/W09ProofEngineering/L08ReadTheType.lean

Introduction "A theorem with `∀ n` in front of it is not ready to apply until
you feed it the specific `n` from the current goal. This level is about that small but
constant proof step."

Statement (P Q : Nat → Prop) :
    (∀ n, P n → Q n) → ∀ n, P n → Q n := by
  Hint "Introduce the concrete `n`, then `specialize` the theorem at that value."
  intro h n hn
  specialize h n
  exact h hn

Conclusion "The quantified theorem was specialized to exactly the case you needed."

NewTactic specialize
OnlyTactic intro specialize exact
