import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 11
Title "Decisions Can Be Enumerated"
-- source: ../game/Game/Worlds/W08Computability/L04DecidableToSemi.lean

Introduction "Every computable predicate is automatically semi-decidable: a total decision
procedure is, in particular, a recognizer for the yes-instances."

Statement {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : ComputablePred p) : SemiDecidable p := by
  Hint "Use `ComputablePred.to_re`."
  exact hp.to_re

Conclusion "Verified: decidable implies semi-decidable."

NewDefinition Game.Complexity.SemiDecidable
NewTheorem ComputablePred.to_re
