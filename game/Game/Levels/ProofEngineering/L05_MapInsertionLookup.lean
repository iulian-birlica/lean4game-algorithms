import Game.Metadata
import Game.Support.ProofEngineering

open Game.ProofEngineering

World "ProofEngineering"
Level 5
Title "Read the Definition"
-- source: ../game/Game/Worlds/W09ProofEngineering/L07MapInsertion.lean

Introduction "When a theorem is really about how a definition unfolds, the
fastest route is usually to open that definition directly. Front insertion into an
association-list map should make the new binding visible immediately."

Statement {κ ν : Type} [BEq κ] [LawfulBEq κ]
    (key : κ) (value : ν) (entries : AssocMap κ ν) :
    AssocMap.lookup key (AssocMap.insert key value entries) = some value := by
  Hint "Unfold both `AssocMap.insert` and `AssocMap.lookup`; the key comparison is
  reflexive."
  unfold AssocMap.insert AssocMap.lookup
  simp only [beq_self_eq_true, if_true]

Conclusion "Unfolded: the freshly inserted binding is found first."

NewDefinition Game.ProofEngineering.AssocMap
  Game.ProofEngineering.AssocMap.lookup
  Game.ProofEngineering.AssocMap.insert
OnlyTactic intro unfold simp
