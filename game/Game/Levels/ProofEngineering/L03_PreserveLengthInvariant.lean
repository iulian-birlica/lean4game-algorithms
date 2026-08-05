import Game.Metadata
import Game.Support.ProofEngineering

open Game.ProofEngineering

World "ProofEngineering"
Level 3
Title "Preserve the Invariant"
-- source: ../game/Game/Worlds/W09ProofEngineering/L05InvariantDesign.lean

Introduction "A good invariant says exactly what must stay true across a state
update. Here the invariant is just equal length, and adding one item to both sides
should preserve it."

Statement {α β : Type} (a : α) (b : β) (left : List α) (right : List β) :
    SameLength left right → SameLength (a :: left) (b :: right) := by
  Hint "Unfold `SameLength`; the old equality turns into the new one after applying
  `Nat.succ` to both sides."
  intro h
  unfold SameLength at h ⊢
  exact congrArg Nat.succ h

Conclusion "The invariant survived the update unchanged."

NewDefinition Game.ProofEngineering.SameLength
NewTactic unfold
OnlyTactic intro unfold exact
