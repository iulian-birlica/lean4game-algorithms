import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 8
Title "Reduction Mirror"
-- source: ../game/Game/Worlds/W08Computability/L01ReductionReflexive.lean

Introduction "A new extension to the computability branch: **many-one reductions**. Start
with the identity case. Every predicate reduces to itself by a total computable map that
preserves answers exactly."

Statement {α : Type*} [Primcodable α] (p : α → Prop) : ManyOne p p := by
  Hint "Use the identity map, `Computable.id`, and `Iff.rfl`."
  exact ⟨id, Computable.id, fun _ => Iff.rfl⟩

Conclusion "Verified: every problem many-one reduces to itself."

NewDefinition Game.Complexity.ManyOne
NewTheorem Computable.id Iff.rfl
