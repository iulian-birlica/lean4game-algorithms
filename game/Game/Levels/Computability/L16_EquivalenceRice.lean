import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 16
Title "Program Equivalence Is Undecidable"
-- source: ../game/Game/Worlds/W08Computability/L09EquivalenceRice.lean

Introduction "Fix any base program. Extensional equivalence with that program is again a
behavioural property, and it is always nontrivial: the base code itself is a yes-witness,
while one of the two constant programs must disagree with it."

Statement (base : Nat.Partrec.Code) : ¬ ComputablePred (EquivalentTo base) := by
  by_cases h0 : base.eval = (Nat.Partrec.Code.const 0).eval
  · have hnot1 : ¬ EquivalentTo base (Nat.Partrec.Code.const 1) := by
      intro hEq
      apply const_zero_ne_const_one
      calc
        (Nat.Partrec.Code.const 0).eval = base.eval := h0.symm
        _ = (Nat.Partrec.Code.const 1).eval := hEq.symm
    simpa [EquivalentTo] using
      (rice_nontrivial
        (C := {c : Nat.Partrec.Code | EquivalentTo base c})
        (invariant := by
          intro cf cg h
          simp [EquivalentTo, h])
        (yes := base)
        (no := Nat.Partrec.Code.const 1)
        (hyes := by simp [EquivalentTo])
        (hno := hnot1))
  · have hnot0 : ¬ EquivalentTo base (Nat.Partrec.Code.const 0) := by
      simpa [EquivalentTo, eq_comm] using h0
    simpa [EquivalentTo] using
      (rice_nontrivial
        (C := {c : Nat.Partrec.Code | EquivalentTo base c})
        (invariant := by
          intro cf cg h
          simp [EquivalentTo, h])
        (yes := base)
        (no := Nat.Partrec.Code.const 0)
        (hyes := by simp [EquivalentTo])
        (hno := hnot0))

Conclusion "Verified: extensional program equivalence is undecidable."

NewDefinition Game.Complexity.EquivalentTo
NewTheorem Game.Complexity.const_zero_ne_const_one
