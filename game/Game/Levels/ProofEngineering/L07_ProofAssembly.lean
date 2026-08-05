import Game.Metadata

World "ProofEngineering"
Level 7
Title "Proof Assembly"
-- source: ../game/Game/Worlds/W09ProofEngineering/L10ProofAssembly.lean

Introduction "Large proofs are often just small facts stitched together in a
readable order. Name the intermediate inequality first, then finish with a `calc`
chain."

Statement (a b c d : Nat) : a ≤ b → b ≤ c → c ≤ d → a ≤ d := by
  Hint "First derive `a ≤ c` from the first two assumptions. Then chain it with
  `c ≤ d`."
  intro hab hbc hcd
  have hac : a ≤ c := Nat.le_trans hab hbc
  calc
    a ≤ c := hac
    _ ≤ d := hcd

Conclusion "Named, chained, finished."

NewTactic «have» «calc»
OnlyTactic intro «have» «calc» exact
