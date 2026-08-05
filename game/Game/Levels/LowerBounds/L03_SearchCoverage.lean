import Game.Metadata
import Game.Support.LowerBounds

World "LowerBounds"
Level 3
Title "Exhaustive Search Lower Bound"
-- source: ../game/Game/Worlds/W14LowerBounds/L03SearchCoverage.lean

Introduction "If every possible target lies in the queried set, then the set
must be at least as large as the whole search space."

Statement (α : Type) [Fintype α] [DecidableEq α] (queried : Finset α) :
    (∀ target, target ∈ queried) → Fintype.card α ≤ queried.card := by
  Hint "Turn the hypothesis into `queried = Finset.univ` and simplify."
  intro h
  have huniv : queried = Finset.univ := Finset.eq_univ_of_forall h
  simp [huniv]

Conclusion "Querying every candidate costs at least the size of the universe."

NewTheorem Finset.eq_univ_of_forall
