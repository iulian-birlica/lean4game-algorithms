import Game.Metadata
import Game.Support.Complexity

open Game.Complexity

World "ComplexityClasses"
Level 11
Title "Hardness Transport"
-- source: ../game/Game/Worlds/W07Complexity/L02HardnessTransport.lean

Introduction "NP-hardness moves **forward** along a reduction: if every `NP` problem reduces to
`source`, and `source` reduces to `target`, then every `NP` problem also reduces to `target`."

Statement {source target : DecisionProblem} :
    NPHard source → Reduces source target → NPHard target := by
  Hint "Expand `NPHard`: for each `NP` source problem, compose the reduction supplied by
  hardness with the given reduction `source → target`."
  intro hsource hreduce problem hproblem
  exact PolyReducible.trans (hsource problem hproblem) hreduce

Conclusion "Verified: reductions transport NP-hardness to later problems."

NewTheorem Game.Complexity.PolyReducible.trans
