import Game.Metadata
import Game.Support.Randomized

open Game.Randomized

World "RandomizedAlgorithms"
Level 2
Title "A Certain Event Has Probability One"
-- source: ../game/Game/Worlds/W10Randomized/L02CertainEvent.lean

Introduction "If every seed makes the event succeed, then a nonempty uniform
experiment assigns that event probability `1`."

Statement (σ : Type) (seeds : List σ) (event : σ → Bool) :
    seeds ≠ [] → (∀ seed ∈ seeds, event seed = true) → probability seeds event = 1 := by
  Hint "Unfold `probability`. Then show `filter event seeds = seeds` because
  every seed satisfies the Boolean test."
  intro h_nonempty h_true
  have hfilter : seeds.filter event = seeds := by
    exact List.filter_eq_self.mpr h_true
  unfold probability
  simp [h_nonempty, eventCount, hfilter]

Conclusion "A sure event now has probability one."

NewDefinition Game.Randomized.probability
NewTactic intro unfold simp
