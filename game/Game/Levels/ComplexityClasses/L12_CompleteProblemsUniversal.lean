import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 12
Title "Complete Problems Are Universal"
-- source: ../game/Game/Worlds/W07Complexity/L03CompleteUniversal.lean

Introduction "An NP-complete problem is **universal for NP**: once `target` is both in `NP` and
NP-hard, every `source ∈ NP` reduces to it."

Statement {source target : DecisionProblem} :
    inNP source → NPComplete target → Reduces source target := by
  Hint "Use the `NPHard` half of the conjunction."
  intro hsource htarget
  exact htarget.2 source hsource

Conclusion "Verified: NP-complete problems receive reductions from every NP problem."
