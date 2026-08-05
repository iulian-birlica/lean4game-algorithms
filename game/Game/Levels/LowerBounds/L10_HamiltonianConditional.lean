import Game.Metadata
import Game.Support.LowerBounds

open Game.Complexity
open Game.AdvancedComplexity

World "LowerBounds"
Level 10
Title "Hamiltonian Path Conditional Lower Bound"
-- source: ../game/Game/Worlds/W14LowerBounds/L10HamiltonianConditional.lean

Introduction "If Hamiltonian path were polynomial-time solvable, then the
supplied SAT-to-Hamiltonian-path reduction would transport that speed back to
SAT and collapse `P` with `NP`."

Statement (cards : HamiltonianReductionCards) :
    NPComplete formulaSATProblem → inP cards.pathProblem → P = NP := by
  Hint "Use the SAT hardness witness from `NPComplete formulaSATProblem`, then
  pull `inP` back through `cards.satToPath`."
  intro hSAT hP
  apply Game.LowerBounds.p_eq_np_of_hard_in_p
  · simpa using hSAT.2
  · exact inP_of_reduces cards.satToPath hP

Conclusion "A fast Hamiltonian-path algorithm would imply `P = NP`."
