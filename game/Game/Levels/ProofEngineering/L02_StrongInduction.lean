import Game.Metadata

World "ProofEngineering"
Level 2
Title "Strong Induction"
-- source: ../game/Game/Worlds/W09ProofEngineering/L04StrongInduction.lean

Introduction "Sometimes the recursive step wants access to every smaller case,
not just the immediate predecessor. This level introduces the strong-induction form of
`induction`."

Statement (n : Nat) : n > 0 → n / 2 < n := by
  Hint "`induction n using Nat.strong_induction_on with` gives a hypothesis for all
  smaller naturals. This particular arithmetic goal then collapses to `omega`."
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      omega

Conclusion "The stronger induction principle is now in your toolkit."

NewTactic induction' omega
OnlyTactic intro induction' omega
