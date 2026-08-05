import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 15
Title "An Atomic SAT Witness"
-- source: ../game/Game/Worlds/W07Complexity/L06SATAtom.lean

Introduction "The SAT mini-language starts with atoms. An atomic formula `.atom name` is
satisfiable: choose an assignment that makes every variable true."

Statement (name : Nat) :
    Formula.Satisfiable (.atom name) := by
  Hint "Exhibit the all-true assignment."
  exact ⟨fun _ => true, rfl⟩

Conclusion "Verified: every single atom has a satisfying assignment."

NewDefinition Game.Complexity.Formula Game.Complexity.Formula.eval
  Game.Complexity.Formula.Satisfiable
