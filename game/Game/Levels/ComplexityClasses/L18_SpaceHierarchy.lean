import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 18
Title "Space-Class Chain"
-- source: ../game/Game/Worlds/W07Complexity/L10SpaceHierarchy.lean

Introduction "Package the standard containments `L ⊆ NL` and `NL ⊆ PSPACE` into the derived
containment `L ⊆ PSPACE`."

Statement (model : SpaceModel) :
    model.L ⊆ model.PSPACE := by
  Hint "Apply the two containment fields in sequence."
  intro problem hproblem
  exact model.nondeterministicLog_is_polynomialSpace
    (model.deterministicLog_is_nondeterministicLog hproblem)

Conclusion "Verified: the space-class chain composes to `L ⊆ PSPACE`."

NewDefinition Game.Complexity.SpaceModel
