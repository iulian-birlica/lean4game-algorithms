import Game.Metadata
import Game.Support.AdvancedComplexity

open Game.Complexity
open Game.AdvancedComplexity

World "AdvancedComplexity"
Level 9
Title "Hamiltonian Completeness"
-- source: ../game/Game/Worlds/W13AdvancedComplexity/L09HamiltonianCompleteness.lean

Introduction "Treat the standard SAT-to-Hamiltonian reductions as theorem
cards: once the cards are supplied, derive NP-completeness of the path and
cycle problems."

Statement hamiltonian_completeness (cards : HamiltonianReductionCards) :
    NPComplete formulaSATProblem →
      NPComplete cards.pathProblem ∧ NPComplete cards.cycleProblem := by
  Hint "For hardness, compose the SAT hardness witness through the supplied
  reduction cards."
  intro hSAT
  refine ⟨?_, ?_⟩
  · refine ⟨cards.path_inNP, ?_⟩
    intro problem hproblem
    exact PolyReducible.trans (hSAT.2 problem hproblem) cards.satToPath
  · refine ⟨cards.cycle_inNP, ?_⟩
    intro problem hproblem
    exact PolyReducible.trans (hSAT.2 problem hproblem)
      (PolyReducible.trans cards.satToPath cards.pathToCycle)

Conclusion "The Hamiltonian path and cycle packages inherit completeness from
SAT."

NewDefinition Game.AdvancedComplexity.HamiltonianReductionCards
