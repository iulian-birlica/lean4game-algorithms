import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 13
Title "Complement Reductions"
-- source: ../game/Game/Worlds/W07Complexity/L04ComplementReduction.lean

Introduction "Many-one reductions survive complementing both problems: if `A ≤ₚ B`, then
`compl A ≤ₚ compl B`. The witness map and its cost bounds do not change; only the correctness
iff is negated."

Statement {source target : DecisionProblem} :
    Reduces source target → Reduces (compl source) (compl target) := by
  Hint "The support lemma `reduceComplements` packages the construction."
  exact fun h => reduceComplements h

Conclusion "Verified: reductions are preserved under complement."

NewDefinition Game.Complexity.inCoNP
NewTheorem Game.Complexity.reduceComplements
