import Game.Metadata
import Game.Support.AdvancedComplexity
import Game.Levels.AdvancedComplexity.L02_CanonicalGates

open Game.Complexity
open Game.AdvancedComplexity

World "AdvancedComplexity"
Level 3
Title "SAT-to-3SAT Forward Direction"
-- source: ../game/Game/Worlds/W13AdvancedComplexity/L03TransformForward.lean

Introduction "A satisfying assignment for the original formula extends to a
satisfying assignment for the Tseitin encoding by making every auxiliary
variable equal to its subformula's value."

Statement tseitin_transform_forward (f : Formula) :
    Formula.Satisfiable f → GenericSatisfiable3 (Tseitin.transform f) := by
  Hint "Extract a satisfying assignment, use the canonical extension, then
  split off the root clause from the gate clauses."
  rintro ⟨a, ha⟩
  refine ⟨Tseitin.canonicalAssignment a, ?_⟩
  simp [Tseitin.transform, evalGenericCNF3]
  refine ⟨?_, ?_⟩
  · unfold evalGenericClause3 Tseitin.clause
    aesop
  · simpa [evalGenericCNF3] using tseitin_gates_complete f a

Conclusion "SAT instances now move forward through the Tseitin transform."

NewDefinition Game.AdvancedComplexity.GenericSatisfiable3
  Game.AdvancedComplexity.Tseitin.transform
