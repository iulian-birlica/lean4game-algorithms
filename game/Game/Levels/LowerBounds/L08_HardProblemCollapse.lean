import Game.Metadata
import Game.Support.LowerBounds

open Game.Complexity

World "LowerBounds"
Level 8
Title "NP-Hardness as a Lower Bound"
-- source: ../game/Game/Worlds/W14LowerBounds/L08HardProblemCollapse.lean

Introduction "Complexity lower bounds can be conditional: if an NP-hard target
were in `P`, then `P = NP`."

Statement (target : DecisionProblem) :
    NPHard target → inP target → P = NP := by
  Hint "Use the packaged collapse theorem from `Game.LowerBounds`."
  intro hard fast
  exact Game.LowerBounds.p_eq_np_of_hard_in_p hard fast

Conclusion "A fast NP-hard algorithm would collapse the central complexity
distinction."

NewTheorem Game.LowerBounds.p_eq_np_of_hard_in_p
