import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L08_BigOCalculus

open Game.Clockwork

World "Asymptotics"
Level 9
Title "Big-Omega Definition"

Introduction "`f =Ω g` means that `f` grows at least as fast as `g`. By
definition, this is just Big-O with the functions reversed."

/-- Big-Omega is Big-O with its arguments reversed. -/
Statement bigOmega_def (f g : ℕ → ℝ) : (f =Ω g) ↔ (g =O f) := by
  Hint "Unfold the definition: `=Ω` was defined to mean exactly `=O` in the
  other direction."
  rfl

Conclusion "Big-Omega is not a new bounding mechanism; it is just the same
eventual inequality read from the opposite side."

NewDefinition Game.Clockwork.IsBigOmega
NewTheorem bigOmega_def
