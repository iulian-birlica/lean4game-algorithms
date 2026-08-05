import Game.Metadata

World "ProofEngineering"
Level 1
Title "Controlled Simplification"
-- source: ../game/Game/Worlds/W09ProofEngineering/L02ControlledSimplification.lean

Introduction "Not every simplification should fire at once. Here the point is
to keep the rewrite set tiny and explicit: only `List.append_nil` is needed."

Statement (xs : List Nat) : (xs ++ []).reverse = xs.reverse := by
  Hint "Use `simp only` with the one named rewrite that removes the trailing `[]`."
  simp only [List.append_nil]

Conclusion "The simplifier stayed on a short leash: one rewrite, goal closed."

NewTactic simp
OnlyTactic intro simp
