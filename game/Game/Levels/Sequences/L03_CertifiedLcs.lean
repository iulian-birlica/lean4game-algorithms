import Game.Metadata
import Game.Support.Design

open Game.Design

World "Sequences"
Level 3
Title "Certified LCS"
-- source: RequestProject Lab07.lcsImpl_correct

Introduction "`lcsCarry` recomputes the LCS while carrying a proof that it
equals the reference `lcs`. Correctness against the specification is a
one-liner: read off the bundled proof."

Statement {α : Type} [DecidableEq α] (xs ys : List α) : lcsImpl xs ys = lcs xs ys := by
  Hint "The proof is bundled with the value inside `lcsCarry`."
  Hint (hidden := true) "`exact (lcsCarry xs ys).2.symm`."
  exact (lcsCarry xs ys).2.symm

Conclusion "Certified: the proof-carrying LCS matches the spec, for free."

NewDefinition Game.Design.lcsImpl Game.Design.lcsCarry
