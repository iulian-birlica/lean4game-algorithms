import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 12
Title "Two Recognizers Make a Decider"
-- source: ../game/Game/Worlds/W08Computability/L05SemiAndCoSemi.lean

Introduction "The standard boundary theorem: a predicate is decidable exactly when both
its yes-instances and its no-instances are recursively enumerable."

Statement {α : Type*} [Primcodable α] (p : α → Prop) :
    ComputablePred p ↔ SemiDecidable p ∧ CoSemiDecidable p := by
  Hint "Use Mathlib's characterization `ComputablePred.computable_iff_re_compl_re'`."
  exact ComputablePred.computable_iff_re_compl_re'

Conclusion "Verified: decidability is equivalent to being both r.e. and co-r.e."

NewDefinition Game.Complexity.CoSemiDecidable
NewTheorem ComputablePred.computable_iff_re_compl_re'
