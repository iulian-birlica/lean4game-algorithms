import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "Computability"
Level 14
Title "Totality Is Undecidable"
-- source: ../game/Game/Worlds/W08Computability/L07TotalityRice.lean

Introduction "Halting on every input is a behavioural property, so Rice's theorem applies.
It is also nontrivial: constant programs are total, while a nowhere-defined program is not."

Statement : ¬ ComputablePred Game.Complexity.Total := by
  rcases exists_empty_code with ⟨c, hc⟩
  simpa using
    (rice_nontrivial
      (C := {d : Nat.Partrec.Code | Game.Complexity.Total d})
      (invariant := by
        intro cf cg h
        constructor
        · intro hcf n
          simpa [Game.Complexity.Total, h] using hcf n
        · intro hcg n
          simpa [Game.Complexity.Total, h] using hcg n)
      (yes := Nat.Partrec.Code.const 0)
      (no := c)
      (hyes := const_total 0)
      (hno := by
        intro htotal
        have hdom : (c.eval 0).Dom := htotal 0
        have hnone : c.eval 0 = Part.none := by
          simpa [Game.Complexity.Empty] using congrFun hc 0
        rw [hnone] at hdom
        simpa using hdom))

Conclusion "Verified: totality is undecidable by Rice's theorem."

NewDefinition Game.Complexity.Total Game.Complexity.Empty
NewTheorem Game.Complexity.rice_nontrivial Game.Complexity.const_total
  Game.Complexity.exists_empty_code
