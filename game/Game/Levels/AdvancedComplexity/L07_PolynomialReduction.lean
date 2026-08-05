import Game.Metadata
import Game.Support.AdvancedComplexity
import Game.Levels.AdvancedComplexity.L05_Equisatisfiable
import Game.Levels.AdvancedComplexity.L06_LinearSize

open Game.Complexity
open Game.AdvancedComplexity

World "AdvancedComplexity"
Level 7
Title "SAT Reduces to 3SAT"
-- source: ../game/Game/Worlds/W13AdvancedComplexity/L07PolynomialReduction.lean

Introduction "Package the correctness theorem and the linear-size bound into a
single polynomial-time many-one reduction."

Statement sat_reduces_tseitin3sat :
    Reduces formulaSATProblem tseitin3SATProblem := by
  Hint "Use `PolyReducible.of_map` with the transformation itself as the map."
  exact PolyReducible.of_map
    Tseitin.transform
    (fun n => 3 * n + 1)
    ⟨4, 1, fun n => by nlinarith⟩
    tseitin_equisatisfiable
    tseitin_linear_size

Conclusion "The Tseitin encoding is now recorded as a polynomial reduction."

NewDefinition Game.AdvancedComplexity.formulaSATProblem
  Game.AdvancedComplexity.tseitin3SATProblem
