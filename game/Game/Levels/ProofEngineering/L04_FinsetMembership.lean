import Game.Metadata

World "ProofEngineering"
Level 4
Title "Finite-Set Membership"
-- source: ../game/Game/Worlds/W09ProofEngineering/L06FiniteSetReasoning.lean

Introduction "Finite-set goals often become easy once you expose the logical
shape of the membership statements. Membership in an intersection gives both sides; a
membership proof for a union only needs one."

Statement (s t : Finset Nat) (x : Nat) : x ∈ s ∩ t → x ∈ s ∪ t := by
  Hint "Rewrite `x ∈ s ∩ t` and `x ∈ s ∪ t` with the corresponding `Finset.mem_*`
  theorems, then keep the left component."
  intro hx
  rw [Finset.mem_inter] at hx
  rw [Finset.mem_union]
  exact Or.inl hx.1

Conclusion "The intersection evidence was enough to enter the union."

OnlyTactic intro rw exact
