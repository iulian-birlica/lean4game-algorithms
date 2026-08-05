import Game.Metadata
import Game.Support.AdvancedComplexity

open Game.AdvancedComplexity

World "AdvancedComplexity"
Level 10
Title "Concrete Machine Inclusion"
-- source: ../game/Game/Worlds/W13AdvancedComplexity/L10ConcreteMachineInclusion.lean

Introduction "If every deterministic transition is also allowed by the
nondeterministic step relation, then every deterministic accepting run is also
a nondeterministic accepting run."

Statement deterministic_run_included {Input : Type} (machine : SpaceMachine Input) :
    machine.DeterministicIncluded →
    ∀ input, machine.deterministicAccepts input → machine.nondeterministicAccepts input := by
  Hint "Reuse the same accepting final state and transport the run with
  `Relation.ReflTransGen.mono`."
  intro hincl input
  rintro ⟨final, hrun, haccept⟩
  exact ⟨final, hrun.mono (fun x y hxy => hincl x y hxy), haccept⟩

Conclusion "Deterministic acceptance is now embedded into nondeterministic
acceptance."

NewDefinition Game.AdvancedComplexity.SpaceMachine
  Game.AdvancedComplexity.SpaceMachine.DeterministicIncluded
  Game.AdvancedComplexity.SpaceMachine.deterministicAccepts
  Game.AdvancedComplexity.SpaceMachine.nondeterministicAccepts
NewTheorem Relation.ReflTransGen.mono
