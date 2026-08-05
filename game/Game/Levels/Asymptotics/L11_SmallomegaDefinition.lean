import Game.Metadata
import Game.Support.Clockwork
import Game.Levels.Asymptotics.L10_SmalloImpliesBigO

open Game.Clockwork

World "Asymptotics"
Level 11
Title "Small-omega Definition"

Introduction "`f =ω g` means that `f` grows strictly faster than `g`. As
with Big-Omega, the definition just reverses the corresponding little-o
relation."

/-- Small-omega is little-o with its arguments reversed. -/
Statement smallomega_def (f g : ℕ → ℝ) : (f =ω g) ↔ (g =o f) := by
  Hint "Unfold the definition."
  rfl

Conclusion "Small-omega is simply the converse viewpoint on little-o."

NewDefinition Game.Clockwork.IsLittleOmega
NewTheorem smallomega_def
