import Game.Metadata
import Game.Support.TableDP

open Game.TableDP

World "TableDynamicProgramming"
Level 3
Title "Edit-Distance Certificate"

Introduction "A DP table entry is useful when it carries both sides of the
correctness story: an alignment that attains the claimed distance, and a proof
that no other alignment is cheaper. Package those two facts as the certificate."

/-- Package edit-distance achievability and optimality into one certificate. -/
Statement {α : Type} {xs ys : List α} {distance : Nat}
    (halign : AlignmentCost xs ys distance)
    (hleast : ∀ candidate, AlignmentCost xs ys candidate → distance ≤ candidate) :
    AlignmentCost xs ys distance ∧
      ∀ candidate, AlignmentCost xs ys candidate → distance ≤ candidate := by
  Hint "The two hypotheses are exactly the two fields of the conjunction."
  exact ⟨halign, hleast⟩

Conclusion "The edit-distance table entry now has both a witness and an optimality proof."

NewTactic exact
