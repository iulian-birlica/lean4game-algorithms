import Game.Metadata
import Game.Support.Complexity

open Game.Complexity
open Cslib.Algorithms.Lean

World "ComplexityClasses"
Level 7
Title "Complement Closure"
-- source: RequestProject Lab20.inP_compl

Introduction "`P` is closed under complementation of the underlying predicate: negate the
solver's Boolean output. That costs one extra step and keeps the running time polynomially
bounded — Lab 19's `IsPolyBounded` closure lemmas do the rest for free."

Statement {L : DecisionProblem} (hL : inP L) : inP (compl L) := by
  Hint "Build the new solver by negating the old one's Boolean return value, keeping the same
  time bound `t`."
  obtain ⟨solve, t, ht, hcorr, htime⟩ := hL
  refine' ⟨fun x => ⟨!(solve x |> TimeM.ret), (solve x |> TimeM.time)⟩, t, ht, _, _⟩ <;>
    simp_all +decide
  · intro x; specialize hcorr x; cases h : (solve x |> TimeM.ret) <;> aesop
  · exact htime

Conclusion "Verified: `P` is closed under complement."

NewDefinition Game.Complexity.compl
