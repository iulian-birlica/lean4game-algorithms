import Game.Metadata
import Game.Support.AdvancedComplexity

open Game.Complexity
open Game.AdvancedComplexity

World "AdvancedComplexity"
Level 6
Title "Linear Clause Bound"
-- source: ../game/Game/Worlds/W13AdvancedComplexity/L06LinearSize.lean

Introduction "The Tseitin transform grows only linearly: each syntax node
contributes a bounded number of clauses."

Statement tseitin_linear_size (f : Formula) :
    (Tseitin.transform f).length ≤ 3 * Tseitin.nodeCount f + 1 := by
  Hint "Induct on `f`, simplify the list lengths, and let arithmetic finish."
  induction f <;> simp_all [Tseitin.transform, Tseitin.gates, Tseitin.nodeCount] <;> omega

Conclusion "The clause blow-up is linear in formula size."

NewDefinition Game.AdvancedComplexity.Tseitin.nodeCount
