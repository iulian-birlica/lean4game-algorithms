import Game.Metadata
import Game.Support.AdvancedComplexity

open Game.AdvancedComplexity
open SignedLiteral

World "AdvancedComplexity"
Level 1
Title "Signed Literal Semantics"
-- source: ../game/Game/Worlds/W13AdvancedComplexity/L01LiteralSemantics.lean

Introduction "Start the Tseitin branch with the smallest moving part: positive
and negative literals. Unfolding `eval`, `pos`, and `neg` should expose both
evaluation rules immediately."

Statement literal_semantics {α : Type} (a : α → Bool) (x : α) :
    eval a (pos x) = a x ∧ eval a (neg x) = !(a x) := by
  Hint "Both halves are definitionally true."
  exact ⟨rfl, rfl⟩

Conclusion "Signed literals now behave exactly like their names suggest."

NewDefinition Game.AdvancedComplexity.SignedLiteral
  Game.AdvancedComplexity.SignedLiteral.eval
  Game.AdvancedComplexity.SignedLiteral.pos
  Game.AdvancedComplexity.SignedLiteral.neg
